module

public import Green64.Library.Sieve.Foundation.Lemma9.Part004
public import Green64.Library.Sieve.Foundation.Lemma9.Part001
public import Green64.Library.PrimeNumberTheoremAnd.MediumPNT
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Green64.Library.Weights.Part006
public import Mathlib
public import Green64.Library.Weights.Part012
public import Green64.Library.Correlation.Part002
public import Green64.Library.Sieve.Foundation.Lemma6.Part003

@[expose] public section

/-!
# Sieve / Foundation / Lemma9 / Part005

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ChenTheorem.Lemma9.BombieriVinogradov.SmallConductorEstimate -/

section

open Filter Real
open scoped Classical Interval

namespace Chen.BombieriVinogradov

/-!
# The small-conductor character estimate

This file absorbs the explicit errors obtained from the finite classical
zero-free contour.  Its endpoint is the Siegel--Walfisz estimate required
for the small primitive-conductor part of Bombieri--Vinogradov.
-/
/-- The unique character at level one turns the twisted von-Mangoldt sum
back into the ordinary Chebyshev `psi` function. -/
theorem twistedPsi_level_one_eq (x : ℕ)
    (χ : DirichletCharacter ℂ 1) :
    twistedPsi x χ = (Chebyshev.psi x : ℂ) := by
  have hχ : χ = 1 := Subsingleton.elim _ _
  subst χ
  have hpsi : (∑ n ∈ Finset.Icc 1 x,
      ArithmeticFunction.vonMangoldt n) = Chebyshev.psi x := by
    rw [Chebyshev.psi_eq_sum_Icc]
    simp only [Nat.floor_natCast]
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hn).2⟩
    · intro n hn hnnot
      have hnData := Finset.mem_Icc.mp hn
      have hn0 : n = 0 := by
        by_contra hnne
        exact hnnot (Finset.mem_Icc.mpr
          ⟨Nat.one_le_iff_ne_zero.mpr hnne, hnData.2⟩)
      subst n
      simp
  unfold twistedPsi
  calc
    ∑ n ∈ Finset.Icc 1 x,
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          (1 : DirichletCharacter ℂ 1) n =
        ∑ n ∈ Finset.Icc 1 x,
          (ArithmeticFunction.vonMangoldt n : ℂ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [MulChar.one_apply]
      · simp
      · rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _]
        exact isUnit_one
    _ = (Chebyshev.psi x : ℂ) := by exact_mod_cast hpsi
/-- Moving to `1 - 1/sqrt(log x)` produces exactly the exponential saving
`exp (-sqrt(log x))`. -/
theorem natCast_rpow_one_sub_inv_sqrt_log_eq
    {x : ℕ} (hx : 2 ≤ x) :
    (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) =
      (x : ℝ) / Real.exp (Real.sqrt (Real.log (x : ℝ))) := by
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by omega)
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) :=
    Real.sqrt_pos.2 hlog
  have hquot : Real.log (x : ℝ) *
      (1 / Real.sqrt (Real.log (x : ℝ))) =
        Real.sqrt (Real.log (x : ℝ)) := by
    rw [mul_one_div, div_eq_iff hsqrt.ne']
    simpa only [pow_two] using (Real.sq_sqrt hlog.le).symm
  rw [Real.rpow_sub hxpos, Real.rpow_one,
    Real.rpow_def_of_pos hxpos, hquot]
/-- Exponential decay in `sqrt(log x)` absorbs an arbitrary fixed power of
`log x`, with an arbitrary fixed leading constant. -/
theorem eventually_const_mul_log_pow_le_exp_sqrt_log
    (C : ℝ) (P : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      C * Real.log (x : ℝ) ^ P ≤
        Real.exp (Real.sqrt (Real.log (x : ℝ))) := by
  have hsqrt : Tendsto
      (fun x : ℕ => Real.sqrt (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hratioReal : ∀ᶠ y : ℝ in atTop,
      C ≤ Real.exp y / y ^ ((2 * P : ℕ) : ℝ) := by
    have hraw := (tendsto_exp_mul_div_rpow_atTop
      (((2 * P : ℕ) : ℝ)) 1 (by norm_num)).eventually
        (eventually_ge_atTop C)
    simpa only [one_mul] using hraw
  have hratio := hsqrt.eventually hratioReal
  have hypos := hsqrt.eventually (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hratio, hypos] with x hx hypos
  let L : ℝ := Real.log (x : ℝ)
  let y : ℝ := Real.sqrt L
  have hL0 : 0 ≤ L := by
    dsimp only [y, L] at hypos ⊢
    exact (Real.sqrt_pos.1 hypos).le
  have hpowpos : 0 < y ^ ((2 * P : ℕ) : ℝ) :=
    Real.rpow_pos_of_pos hypos _
  have hmain : C * y ^ ((2 * P : ℕ) : ℝ) ≤ Real.exp y :=
    (le_div_iff₀ hpowpos).mp (by simpa only [y, L] using hx)
  have hLpow : L ^ P = y ^ (2 * P) := by
    rw [show L = y ^ 2 by
      dsimp only [y]
      exact (Real.sq_sqrt hL0).symm]
    rw [← pow_mul]
  calc
    C * Real.log (x : ℝ) ^ P = C * L ^ P := by rfl
    _ = C * y ^ (2 * P) := by rw [hLpow]
    _ = C * y ^ ((2 * P : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    _ ≤ Real.exp y := hmain
    _ = Real.exp (Real.sqrt (Real.log (x : ℝ))) := by rfl
/-- The medium-strength prime-number-theorem decay beats every inverse
power of the logarithm. -/
theorem eventually_exp_neg_mul_log_rpow_le_log_inv_pow
    {c : ℝ} (hc : 0 < c) (K : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      Real.exp (-c * Real.log (x : ℝ) ^ ((1 : ℝ) / 10)) ≤
        (Real.log (x : ℝ) ^ K)⁻¹ := by
  have hyT : Tendsto
      (fun x : ℕ => Real.log (x : ℝ) ^ ((1 : ℝ) / 10))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hratioReal : ∀ᶠ y : ℝ in atTop,
      1 ≤ Real.exp (c * y) / y ^ ((10 * K : ℕ) : ℝ) :=
    (tendsto_exp_mul_div_rpow_atTop
      (((10 * K : ℕ) : ℝ)) c hc).eventually
        (eventually_ge_atTop 1)
  filter_upwards [hyT.eventually hratioReal,
      hyT.eventually (eventually_gt_atTop 0),
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop 0)] with x hratio hypos hlog
  change 0 < Real.log (x : ℝ) at hlog
  let L : ℝ := Real.log (x : ℝ)
  let y : ℝ := L ^ ((1 : ℝ) / 10)
  have hpowpos : 0 < y ^ ((10 * K : ℕ) : ℝ) :=
    Real.rpow_pos_of_pos (by simpa only [y, L] using hypos) _
  have hratio' : 1 ≤ Real.exp (c * y) /
      y ^ ((10 * K : ℕ) : ℝ) := by
    simpa only [y, L] using hratio
  have hmain : y ^ ((10 * K : ℕ) : ℝ) ≤ Real.exp (c * y) := by
    simpa only [one_mul] using (le_div_iff₀ hpowpos).mp hratio'
  have hLpow : L ^ K = y ^ ((10 * K : ℕ) : ℝ) := by
    calc
      L ^ K = L ^ (K : ℝ) := (Real.rpow_natCast L K).symm
      _ = L ^ (((1 : ℝ) / 10) * (10 * K : ℕ)) := by
        congr 1
        push_cast
        ring
      _ = (L ^ ((1 : ℝ) / 10)) ^ ((10 * K : ℕ) : ℝ) :=
        Real.rpow_mul (by positivity) _ _
      _ = y ^ ((10 * K : ℕ) : ℝ) := by rfl
  have hmain' : L ^ K ≤ Real.exp (c * y) := hLpow.trans_le hmain
  have hLpowpos : 0 < L ^ K := pow_pos (by simpa only [L] using hlog) _
  have hexppos : 0 < Real.exp (c * y) := Real.exp_pos _
  calc
    Real.exp (-c * Real.log (x : ℝ) ^ ((1 : ℝ) / 10)) =
        (Real.exp (c * y))⁻¹ := by
      rw [← Real.exp_neg]
      dsimp only [y, L]
      congr 1
      ring
    _ ≤ (L ^ K)⁻¹ := (inv_le_inv₀ hexppos hLpowpos).mpr hmain'
    _ = (Real.log (x : ℝ) ^ K)⁻¹ := by rfl
/-- The ordinary prime number theorem supplies the missing level-one
character estimate with any inverse logarithmic saving. -/
theorem abs_psi_sub_self_log_pow_bound (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      |Chebyshev.psi x - (x : ℝ)| ≤
        C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
  obtain ⟨c, hc, hpnt⟩ := MediumPNT
  rw [Asymptotics.isBigO_iff] at hpnt
  obtain ⟨M, hM⟩ := hpnt
  let C : ℝ := |M| + 1
  have hCpos : 0 < C := by dsimp only [C]; linarith [abs_nonneg M]
  have hMn := tendsto_natCast_atTop_atTop.eventually hM
  have hdecay := eventually_exp_neg_mul_log_rpow_le_log_inv_pow hc K
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [eventually_ge_atTop 2, hMn, hdecay] with
      x hx hM hdecay
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hLpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hfactor0 : 0 ≤ (x : ℝ) *
      Real.exp (-c * Real.log (x : ℝ) ^ ((1 : ℝ) / 10)) := by
    positivity
  have hraw : |Chebyshev.psi x - (x : ℝ)| ≤
      M * ((x : ℝ) *
        Real.exp (-c * Real.log (x : ℝ) ^ ((1 : ℝ) / 10))) := by
    simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs,
      abs_of_nonneg hfactor0] using hM
  calc
    |Chebyshev.psi x - (x : ℝ)| ≤
        M * ((x : ℝ) *
          Real.exp (-c * Real.log (x : ℝ) ^ ((1 : ℝ) / 10))) := hraw
    _ ≤ C * ((x : ℝ) *
          Real.exp (-c * Real.log (x : ℝ) ^ ((1 : ℝ) / 10))) :=
      mul_le_mul_of_nonneg_right
        (show M ≤ C by dsimp only [C]; linarith [le_abs_self M]) hfactor0
    _ ≤ C * ((x : ℝ) * (Real.log (x : ℝ) ^ K)⁻¹) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdecay hx0) hCpos.le
    _ = C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
      rw [div_eq_mul_inv]
      ring
/-- At level one, `adjustedTwistedPsi` is exactly the ordinary PNT error. -/
theorem norm_adjustedTwistedPsi_level_one_bound (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ χ : DirichletCharacter ℂ 1,
        ‖adjustedTwistedPsi x χ‖ ≤
          C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
  obtain ⟨C, hC, hpnt⟩ := abs_psi_sub_self_log_pow_bound K
  refine ⟨C, hC, ?_⟩
  filter_upwards [hpnt] with x hpnt
  intro χ
  have hχ : χ = 1 := Subsingleton.elim _ _
  rw [adjustedTwistedPsi, if_pos hχ, twistedPsi_level_one_eq]
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using hpnt
/-- A convenient quotient form of the preceding absorption lemma. -/
theorem eventually_const_mul_shifted_rpow_mul_log_pow_le
    (C : ℝ) (P K : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      C * (x : ℝ) ^
          (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
          Real.log (x : ℝ) ^ P ≤
        (x : ℝ) / Real.log (x : ℝ) ^ K := by
  have habsorb := eventually_const_mul_log_pow_le_exp_sqrt_log
    C (P + K)
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2, habsorb,
      hlogT.eventually (eventually_gt_atTop 0)] with x hx habsorb hlog
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hexp : 0 < Real.exp (Real.sqrt (Real.log (x : ℝ))) :=
    Real.exp_pos _
  have hKpos : 0 < Real.log (x : ℝ) ^ K := pow_pos hlog _
  rw [natCast_rpow_one_sub_inv_sqrt_log_eq hx]
  rw [le_div_iff₀ hKpos]
  have hscale := mul_le_mul_of_nonneg_left habsorb
    (div_nonneg hx0 hexp.le)
  calc
    C * ((x : ℝ) / Real.exp (Real.sqrt (Real.log (x : ℝ)))) *
          Real.log (x : ℝ) ^ P * Real.log (x : ℝ) ^ K =
        ((x : ℝ) / Real.exp (Real.sqrt (Real.log (x : ℝ)))) *
          (C * Real.log (x : ℝ) ^ (P + K)) := by
      rw [pow_add]
      ring
    _ ≤ ((x : ℝ) /
          Real.exp (Real.sqrt (Real.log (x : ℝ)))) *
        Real.exp (Real.sqrt (Real.log (x : ℝ))) := hscale
    _ = (x : ℝ) := by field_simp [hexp.ne']
/-- If `p + k ≤ n`, an inverse `n`-th power dominates the requested
inverse `k`-th power after paying a numerator power `p`. -/
theorem mul_pow_mul_inv_pow_le_div_pow
    {X L : ℝ} (hX : 0 ≤ X) (hL : 1 ≤ L)
    {p n k : ℕ} (hpn : p + k ≤ n) :
    X * L ^ p * (L ^ n)⁻¹ ≤ X / L ^ k := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hpow : L ^ (p + k) ≤ L ^ n :=
    pow_le_pow_right₀ hL hpn
  have hinv : (L ^ n)⁻¹ ≤ (L ^ (p + k))⁻¹ :=
    (inv_le_inv₀ (pow_pos hLpos _) (pow_pos hLpos _)).mpr hpow
  calc
    X * L ^ p * (L ^ n)⁻¹ ≤
        X * L ^ p * (L ^ (p + k))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv
        (mul_nonneg hX (pow_nonneg hLpos.le _))
    _ = X * (L ^ k)⁻¹ := by
      rw [pow_add]
      field_simp [hLpos.ne']
    _ = X / L ^ k := by rw [div_eq_mul_inv]
/-- The complete logarithmic-derivative integral for one primitive small
conductor has an arbitrary logarithmic saving.  This is where the
exponential gain from the shifted vertical side absorbs its growing
polylogarithmic height. -/
theorem norm_integral_bvSmoothedLogDeriv_smallConductor_bound
    {E : ℕ} (data : Chen.PrimitiveZeroFreeRegionDataAt E) (K R : ℕ)
    (hR : 1 ≤ R) (hER : 3 * R ≤ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        2 ≤ q → (q : ℝ) ≤ Real.log (x : ℝ) ^ R →
          χ.IsPrimitive →
          ‖∫ t : ℝ,
              bvSmoothedLogDerivIntegrand K x χ
                (Chen.lemma6AlphaPoint x t)‖ ≤
            C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
  let N : ℕ := 22 * (K + 1)
  let D : ℝ := (((N + R + 4 : ℕ) : ℝ) ^ 2) * data.cLogDeriv
  let C : ℝ := 1 + 4 * Real.exp 1 * D + 4 * Real.exp 1 * Real.pi
  have hDpos : 0 < D := by
    dsimp only [D, N]
    exact mul_pos (by positivity) data.cLogDeriv_pos
  have hCpos : 0 < C := by
    dsimp only [C]
    positivity
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hwidthAll :=
    eventually_two_div_sqrt_log_lt_primitiveZeroFreeWidth_bvHeight
      data K R hR hER
  have habsorb := eventually_const_mul_shifted_rpow_mul_log_pow_le
    (4 * D) (N + 2) K
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [eventually_ge_atTop 2,
      hlogT.eventually (eventually_ge_atTop 10), hwidthAll, habsorb] with
      x hx hLten hwidthAll habsorb
  intro q _ χ hq hqR hχ
  let L : ℝ := Real.log (x : ℝ)
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)) := by
    have hfirst : (10 : ℝ) ^ 4 ≤ L ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hLten 4
    have hsecond : L ^ 4 ≤ L ^ (10 * (K + 1)) :=
      pow_le_pow_right₀ hLone (by omega)
    simpa only [L] using hfirst.trans hsecond
  have hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)) := by
    have hsqrt : (2 : ℝ) ≤ Real.sqrt L := by
      have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
      rw [← hsqrt4]
      exact Real.sqrt_le_sqrt (by linarith)
    have hinv : 1 / Real.sqrt L ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hsqrt
    dsimp only [L] at hinv ⊢
    linarith
  have hwidth : ∀ t : ℝ, |t| ≤ bvSmoothingContourHeight K x →
      2 / Real.sqrt (Real.log (x : ℝ)) <
        Chen.primitiveZeroFreeWidthAt E data.cHeight data.cSiegel q t :=
    hwidthAll q hq hqR
  have hfinite :=
    norm_integral_bvSmoothedLogDeriv_alpha_le_finite_classical
      data K hq hx hlarge hγpos hχ hwidth
  have hheight : bvSmoothingContourHeight K x = L ^ N := by
    dsimp only [bvSmoothingContourHeight, L, N]
    rw [← pow_mul]
    congr 1
    omega
  have hM : Chen.primitiveLogDerivMajorantAt data q
        (bvSmoothingContourHeight K x) ≤ D * L ^ 2 := by
    have hm := eq21ClassicalLogDerivMajorant_bvHeight_le
      data K R hR hER
        (by simpa only [L] using (show (4 : ℝ) ≤ L by linarith))
        hq hqR
    simpa only [D, N, L] using hm
  have hM0 := Chen.primitiveLogDerivMajorantAt_nonneg data q
    (bvSmoothingContourHeight K x)
  have hwidthOne :
      |(1 + 1 / Real.log (x : ℝ)) -
        (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| ≤ 1 := by
    have hinvlog : 0 ≤ 1 / L := by positivity
    have hinvsqrt : 0 ≤ 1 / Real.sqrt L := by positivity
    have hsqrt : 1 / Real.sqrt L ≤ 1 / 2 := by
      linarith [hγpos]
    have hloginv : 1 / L ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    dsimp only [L] at hinvlog hinvsqrt hsqrt hloginv ⊢
    rw [abs_of_nonneg (by linarith)]
    linarith
  let Y : ℝ := (x : ℝ) / L ^ K
  have hY0 : 0 ≤ Y := by dsimp only [Y]; positivity
  have hB1 :
      4 * bvSmoothingContourHeight K x *
          ((x : ℝ) ^
            (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
            Chen.primitiveLogDerivMajorantAt data q
              (bvSmoothingContourHeight K x)) ≤ Y := by
    calc
      4 * bvSmoothingContourHeight K x *
          ((x : ℝ) ^
            (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
            Chen.primitiveLogDerivMajorantAt data q
              (bvSmoothingContourHeight K x)) ≤
        4 * bvSmoothingContourHeight K x *
          ((x : ℝ) ^
            (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
            (D * L ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hM (Real.rpow_nonneg hx0 _))
            (mul_nonneg (by norm_num)
              (bvSmoothingContourHeight_nonneg K x))
      _ = 4 * L ^ N *
          ((x : ℝ) ^
            (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
            (D * L ^ 2)) := by rw [hheight]
      _ = (4 * D) * (x : ℝ) ^
          (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
            L ^ (N + 2) := by
        rw [pow_add]
        ring
      _ ≤ Y := by simpa only [L, N, Y] using habsorb
  have hX2 : 0 ≤ 4 * Real.exp 1 * D * (x : ℝ) := by positivity
  have hpow2 := mul_pow_mul_inv_pow_le_div_pow hX2 hLone
    (p := 2) (n := 44 * (K + 1)) (k := K) (by omega)
  have hB2 :
      2 * (((2 * Real.exp 1 * (x : ℝ) *
          Chen.primitiveLogDerivMajorantAt data q
            (bvSmoothingContourHeight K x)) *
          (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) *
        |(1 + 1 / Real.log (x : ℝ)) -
          (1 - 1 / Real.sqrt (Real.log (x : ℝ)))|) ≤
        (4 * Real.exp 1 * D) * Y := by
    have hinv0 : 0 ≤
        (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹ := by positivity
    have hcoef0 : 0 ≤ 2 * Real.exp 1 * (x : ℝ) := by positivity
    have hZ0 : 0 ≤
        (2 * Real.exp 1 * (x : ℝ) *
          Chen.primitiveLogDerivMajorantAt data q
            (bvSmoothingContourHeight K x)) *
          (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹ :=
      mul_nonneg (mul_nonneg hcoef0 hM0) hinv0
    have hZM :
        (2 * Real.exp 1 * (x : ℝ) *
          Chen.primitiveLogDerivMajorantAt data q
            (bvSmoothingContourHeight K x)) *
            (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹ ≤
          (2 * Real.exp 1 * (x : ℝ) * (D * L ^ 2)) *
            (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hM hcoef0) hinv0
    calc
      2 * (((2 * Real.exp 1 * (x : ℝ) *
          Chen.primitiveLogDerivMajorantAt data q
            (bvSmoothingContourHeight K x)) *
          (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) *
        |(1 + 1 / Real.log (x : ℝ)) -
          (1 - 1 / Real.sqrt (Real.log (x : ℝ)))|) ≤
        2 * (((2 * Real.exp 1 * (x : ℝ) *
          Chen.primitiveLogDerivMajorantAt data q
            (bvSmoothingContourHeight K x)) *
          (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hwidthOne hZ0) (by norm_num)
      _ ≤ 2 * (((2 * Real.exp 1 * (x : ℝ) * (D * L ^ 2)) *
          (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hZM (by norm_num)) (by norm_num)
      _ =
        (4 * Real.exp 1 * D * (x : ℝ)) * L ^ 2 *
          (L ^ (44 * (K + 1)))⁻¹ := by
        dsimp only [L]
        ring
      _ ≤ (4 * Real.exp 1 * D * (x : ℝ)) / L ^ K := hpow2
      _ = (4 * Real.exp 1 * D) * Y := by
        dsimp only [Y]
        ring
  have hX3 : 0 ≤ 4 * Real.exp 1 * Real.pi * (x : ℝ) := by positivity
  have hpow3 := mul_pow_mul_inv_pow_le_div_pow hX3 hLone
    (p := 2) (n := 11 * (K + 1)) (k := K) (by omega)
  have hB3 :
      (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
          ((Real.log (x : ℝ) ^ (11 * (K + 1)))⁻¹ * Real.pi) ≤
        (4 * Real.exp 1 * Real.pi) * Y := by
    calc
      (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
          ((Real.log (x : ℝ) ^ (11 * (K + 1)))⁻¹ * Real.pi) =
        (4 * Real.exp 1 * Real.pi * (x : ℝ)) * L ^ 2 *
          (L ^ (11 * (K + 1)))⁻¹ := by
        dsimp only [L]
        ring
      _ ≤ (4 * Real.exp 1 * Real.pi * (x : ℝ)) / L ^ K := hpow3
      _ = (4 * Real.exp 1 * Real.pi) * Y := by
        dsimp only [Y]
        ring
  apply hfinite.trans
  calc
    4 * bvSmoothingContourHeight K x *
          ((x : ℝ) ^
            (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
            Chen.primitiveLogDerivMajorantAt data q
              (bvSmoothingContourHeight K x)) +
        2 * (((2 * Real.exp 1 * (x : ℝ) *
            Chen.primitiveLogDerivMajorantAt data q
              (bvSmoothingContourHeight K x)) *
            (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) *
          |(1 + 1 / Real.log (x : ℝ)) -
            (1 - 1 / Real.sqrt (Real.log (x : ℝ)))|) +
        (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
          ((Real.log (x : ℝ) ^ (11 * (K + 1)))⁻¹ * Real.pi) ≤
      Y + (4 * Real.exp 1 * D) * Y +
        (4 * Real.exp 1 * Real.pi) * Y := by
      exact add_le_add (add_le_add hB1 hB2) hB3
    _ = C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
      dsimp only [C, Y, L]
      ring
/-- The adjustable smoothed twisted von-Mangoldt sum inherits the same
arbitrary logarithmic saving from its Perron representation. -/
theorem norm_bvSmoothedTwistedPsi_smallConductor_bound
    {E : ℕ} (data : Chen.PrimitiveZeroFreeRegionDataAt E) (K R : ℕ)
    (hR : 1 ≤ R) (hER : 3 * R ≤ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        2 ≤ q → (q : ℝ) ≤ Real.log (x : ℝ) ^ R →
          χ.IsPrimitive →
          ‖bvSmoothedTwistedPsi K x χ‖ ≤
            C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
  obtain ⟨C, hC, hbound⟩ :=
    norm_integral_bvSmoothedLogDeriv_smallConductor_bound
      data K R hR hER
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop 2, hbound,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop 10)] with x hx hbound hlog
  intro q _ χ hq hqR hχ
  change 10 ≤ Real.log (x : ℝ) at hlog
  have hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)) := by
    have hLone : (1 : ℝ) ≤ Real.log (x : ℝ) := by linarith
    exact (pow_le_pow_left₀ (by norm_num) hlog 4).trans
      (pow_le_pow_right₀ hLone (by omega))
  have hint := hbound q χ hq hqR hχ
  rw [bvSmoothedTwistedPsi_eq_logDerivPerron K hx hlarge χ]
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  have hnormalize :
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
          (Complex.I * ∫ t : ℝ,
            bvSmoothedLogDerivIntegrand K x χ
              (((1 + 1 / Real.log (x : ℝ) : ℝ) : ℂ) +
                (t : ℂ) * Complex.I)) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, bvSmoothedLogDerivIntegrand K x χ
            (Chen.lemma6AlphaPoint x t) := by
    have hconst :
        (1 / (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I =
          ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
      calc
        (1 / (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I =
            1 / (2 * (Real.pi : ℂ)) := by
          field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
        _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by norm_cast
    unfold Chen.lemma6AlphaPoint
    rw [← mul_assoc, hconst]
  rw [hnormalize, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  have hscalar : 1 / (2 * Real.pi) ≤ (1 : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    linarith [Real.pi_gt_three]
  exact (mul_le_of_le_one_left (norm_nonneg _) hscalar).trans hint
/-- The adjustable smoothing parameter is so large that its residual
`R^(-1/10)` error beats any prescribed inverse logarithmic power. -/
theorem eventually_bvSmoothingParameter_neg_tenth_le_log_inv_pow
    (K : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      bvSmoothingParameter K x ^ (-(0.1 : ℝ)) ≤
        (Real.log (x : ℝ) ^ K)⁻¹ := by
  have habsorb := Chen.eventually_const_mul_log_pow_le_rpow
    1 K (by norm_num : (0 : ℝ) < 0.1)
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2, habsorb,
      hlogT.eventually (eventually_ge_atTop 1)] with x hx habsorb hlog
  let L : ℝ := Real.log (x : ℝ)
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by omega)
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by simpa only [L] using hlog
  have hRpos : 0 < bvSmoothingParameter K x := by
    unfold bvSmoothingParameter
    exact Real.exp_pos _
  have hExp : (x : ℝ) ^ (0.1 : ℝ) ≤
      bvSmoothingParameter K x ^ (0.1 : ℝ) := by
    rw [Real.rpow_def_of_pos hxpos,
      Real.rpow_def_of_pos hRpos, log_bvSmoothingParameter]
    apply Real.exp_le_exp.mpr
    have hpow : L ≤ L ^ (10 * (K + 1)) := by
      calc
        L = L ^ 1 := by ring
        _ ≤ L ^ (10 * (K + 1)) :=
          pow_le_pow_right₀ hLone (by omega)
    dsimp only [L] at hpow ⊢
    nlinarith
  have hlogpow : Real.log (x : ℝ) ^ K ≤
      (x : ℝ) ^ (0.1 : ℝ) := by
    simpa only [one_mul] using habsorb
  have htotal : Real.log (x : ℝ) ^ K ≤
      bvSmoothingParameter K x ^ (0.1 : ℝ) := hlogpow.trans hExp
  rw [show bvSmoothingParameter K x ^ (-(0.1 : ℝ)) =
      (bvSmoothingParameter K x ^ (0.1 : ℝ))⁻¹ by
    simpa only using Real.rpow_neg hRpos.le (0.1 : ℝ)]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hRpos _)
    (pow_pos hLpos K)).mpr htotal
/-- The difference between the sharp and adjustable smoothed sums also has
an arbitrary logarithmic saving, uniformly in the character and modulus. -/
theorem norm_twistedPsi_sub_bvSmoothedTwistedPsi_smallConductor_bound
    (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        ‖twistedPsi x χ - bvSmoothedTwistedPsi K x χ‖ ≤
          C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
  let C : ℝ := Real.log 4 + 7
  have hCpos : 0 < C := by
    dsimp only [C]
    have : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hRerr := eventually_bvSmoothingParameter_neg_tenth_le_log_inv_pow K
  have hlogabsorb := Chen.eventually_const_mul_log_pow_le_rpow
    1 (K + 1) (by norm_num : (0 : ℝ) < 1)
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [eventually_ge_atTop 2, hRerr, hlogabsorb,
      hlogT.eventually (eventually_ge_atTop 10)] with
      x hx hRerr hlogabsorb hLten
  intro q χ
  let L : ℝ := Real.log (x : ℝ)
  let Y : ℝ := (x : ℝ) / L ^ K
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have hY0 : 0 ≤ Y := by dsimp only [Y]; positivity
  have hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)) := by
    have hfirst : (10 : ℝ) ^ 4 ≤ L ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hLten 4
    have hsecond : L ^ 4 ≤ L ^ (10 * (K + 1)) :=
      pow_le_pow_right₀ hLone (by omega)
    simpa only [L] using hfirst.trans hsecond
  have hpsi : Chebyshev.psi x ≤ (Real.log 4 + 4) * (x : ℝ) :=
    Chebyshev.psi_le_const_mul_self hx0
  have hpsi0 : 0 ≤ Chebyshev.psi x := by positivity
  have hdeep : bvSmoothingParameter K x ^ (-(0.1 : ℝ)) *
      Chebyshev.psi x ≤ (Real.log 4 + 4) * Y := by
    calc
      bvSmoothingParameter K x ^ (-(0.1 : ℝ)) *
          Chebyshev.psi x ≤
        (L ^ K)⁻¹ * Chebyshev.psi x :=
          mul_le_mul_of_nonneg_right
            (by simpa only [L] using hRerr) hpsi0
      _ ≤ (L ^ K)⁻¹ * ((Real.log 4 + 4) * (x : ℝ)) :=
        mul_le_mul_of_nonneg_left hpsi (by positivity)
      _ = (Real.log 4 + 4) * Y := by
        dsimp only [Y]
        rw [div_eq_mul_inv]
        ring
  have hrpowBoundary : L ^ (-(K + 1 : ℝ)) * L = (L ^ K)⁻¹ := by
    calc
      L ^ (-(K + 1 : ℝ)) * L =
          L ^ (-(K + 1 : ℝ)) * L ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = L ^ (-(K + 1 : ℝ) + 1) := by
        rw [Real.rpow_add hLpos]
      _ = L ^ (-(K : ℝ)) := by
        congr 1
        ring
      _ = (L ^ (K : ℝ))⁻¹ := Real.rpow_neg hLpos.le _
      _ = (L ^ K)⁻¹ := by rw [Real.rpow_natCast]
  have hlogpow : L ^ (K + 1) ≤ (x : ℝ) := by
    simpa only [one_mul, Real.rpow_one, L] using hlogabsorb
  have hLY : L ≤ Y := by
    rw [show Y = (x : ℝ) / L ^ K by rfl,
      le_div_iff₀ (pow_pos hLpos K)]
    calc
      L * L ^ K = L ^ (K + 1) := by rw [pow_succ']
      _ ≤ (x : ℝ) := hlogpow
  have hboundary :
      (2 * (x : ℝ) * Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) + 1) *
          Real.log (x : ℝ) ≤ 3 * Y := by
    calc
      (2 * (x : ℝ) * Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) + 1) *
          Real.log (x : ℝ) =
        2 * (x : ℝ) * (L ^ K)⁻¹ + L := by
          dsimp only [L]
          calc
            (2 * (x : ℝ) * Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) + 1) *
                Real.log (x : ℝ) =
              2 * (x : ℝ) *
                  (Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) *
                    Real.log (x : ℝ)) + Real.log (x : ℝ) := by ring
            _ = 2 * (x : ℝ) * (Real.log (x : ℝ) ^ K)⁻¹ +
                Real.log (x : ℝ) := by rw [hrpowBoundary]
      _ = 2 * Y + L := by
        dsimp only [Y]
        rw [div_eq_mul_inv]
        ring
      _ ≤ 2 * Y + Y := by linarith
      _ = 3 * Y := by ring
  have hraw := norm_twistedPsi_sub_bvSmoothedTwistedPsi_le_explicit
    K hx hlarge χ
  apply hraw.trans
  calc
    bvSmoothingParameter K x ^ (-(0.1 : ℝ)) * Chebyshev.psi x +
        (2 * (x : ℝ) * Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) + 1) *
          Real.log (x : ℝ) ≤
      (Real.log 4 + 4) * Y + 3 * Y := add_le_add hdeep hboundary
    _ = C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
      dsimp only [C, Y, L]
      ring
/-- **Siegel--Walfisz for the primitive characters needed by
Bombieri--Vinogradov.**  Every fixed inverse logarithmic power is available,
uniformly for conductors `q ≤ (log x)^R`, for every fixed `R`. -/
theorem norm_twistedPsi_smallConductor_bound
    (hzf : Chen.PrimitiveZeroFreeRegion) (K R : ℕ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        2 ≤ q → (q : ℝ) ≤ Real.log (x : ℝ) ^ R →
          χ.IsPrimitive →
          ‖twistedPsi x χ‖ ≤
            C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
  rw [Chen.PrimitiveZeroFreeRegion] at hzf
  obtain ⟨data⟩ := hzf.2 (3 * R) (by omega)
  obtain ⟨C₁, hC₁, hsmooth⟩ :=
    norm_bvSmoothedTwistedPsi_smallConductor_bound
      data K R hR (by omega)
  obtain ⟨C₂, hC₂, herr⟩ :=
    norm_twistedPsi_sub_bvSmoothedTwistedPsi_smallConductor_bound K
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  filter_upwards [hsmooth, herr,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop 0)] with x hsmooth herr hlog
  intro q _ χ hq hqR hχ
  have hS := hsmooth q χ hq hqR hχ
  have hE := herr q χ
  have hY0 : 0 ≤ (x : ℝ) / Real.log (x : ℝ) ^ K := by positivity
  calc
    ‖twistedPsi x χ‖ =
        ‖(twistedPsi x χ - bvSmoothedTwistedPsi K x χ) +
          bvSmoothedTwistedPsi K x χ‖ := by ring_nf
    _ ≤ ‖twistedPsi x χ - bvSmoothedTwistedPsi K x χ‖ +
        ‖bvSmoothedTwistedPsi K x χ‖ := norm_add_le _ _
    _ ≤ C₂ * (x : ℝ) / Real.log (x : ℝ) ^ K +
        C₁ * (x : ℝ) / Real.log (x : ℝ) ^ K :=
      add_le_add hE hS
    _ = (C₁ + C₂) * (x : ℝ) /
        Real.log (x : ℝ) ^ K := by ring
/-- For primitive moduli at least two, the principal correction vanishes,
so the same small-conductor estimate holds for `adjustedTwistedPsi`. -/
theorem norm_adjustedTwistedPsi_smallConductor_bound
    (hzf : Chen.PrimitiveZeroFreeRegion) (K R : ℕ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        2 ≤ q → (q : ℝ) ≤ Real.log (x : ℝ) ^ R →
          χ.IsPrimitive →
          ‖adjustedTwistedPsi x χ‖ ≤
            C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
  obtain ⟨C, hC, hbound⟩ :=
    norm_twistedPsi_smallConductor_bound hzf K R hR
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with x hbound
  intro q _ χ hq hqR hχ
  rw [adjustedTwistedPsi, if_neg (Chen.primitiveCharacter_ne_one hq hχ),
    sub_zero]
  exact hbound q χ hq hqR hχ
/-- If every primitive character of conductor at most `H` is bounded by
`M`, then the reciprocal-totient weights cancel the number of characters
and the whole small-conductor mean is at most `H * M`. -/
theorem primitiveAdjustedMean_le_mul_of_character_bound
    (x H : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hchar : ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q), q ≤ H → χ.IsPrimitive →
        ‖adjustedTwistedPsi x χ‖ ≤ M) :
    primitiveAdjustedMean x 0 H ≤ (H : ℝ) * M := by
  rw [primitiveAdjustedMean]
  calc
    (∑ q ∈ Finset.Ioc 0 H, (Nat.totient q : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖adjustedTwistedPsi x χ‖ else 0) ≤
        ∑ _q ∈ Finset.Ioc 0 H, M := by
      apply Finset.sum_le_sum
      intro q hqmem
      have hqdata := Finset.mem_Ioc.mp hqmem
      letI : NeZero q := ⟨by omega⟩
      have hpoint :
          ∀ χ : DirichletCharacter ℂ q,
            (if χ.IsPrimitive then ‖adjustedTwistedPsi x χ‖ else 0) ≤ M := by
        intro χ
        by_cases hχ : χ.IsPrimitive
        · rw [if_pos hχ]
          exact hchar q χ hqdata.2 hχ
        · rw [if_neg hχ]
          exact hM
      have hsum :
          (∑ χ : DirichletCharacter ℂ q,
              if χ.IsPrimitive then ‖adjustedTwistedPsi x χ‖ else 0) ≤
            ∑ _χ : DirichletCharacter ℂ q, M :=
        Finset.sum_le_sum fun χ _ => hpoint χ
      have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      have htot : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr hqdata.1
      calc
        (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q,
              if χ.IsPrimitive then ‖adjustedTwistedPsi x χ‖ else 0) ≤
            (q.totient : ℝ)⁻¹ *
              ∑ _χ : DirichletCharacter ℂ q, M :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr htot.le)
        _ = M := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
          field_simp
    _ = ((Finset.Ioc 0 H).card : ℝ) * M := by simp
    _ = (H : ℝ) * M := by simp
/-- The primitive small-conductor mean inherits an arbitrary logarithmic
saving, with the number of conductors displayed explicitly. -/
theorem primitiveAdjustedMean_smallConductor_bound
    (hzf : Chen.PrimitiveZeroFreeRegion) (K R : ℕ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ H : ℕ,
        (H : ℝ) ≤ Real.log (x : ℝ) ^ R →
          primitiveAdjustedMean x 0 H ≤
            C * (H : ℝ) * (x : ℝ) /
              Real.log (x : ℝ) ^ K := by
  obtain ⟨C₁, hC₁, hone⟩ := norm_adjustedTwistedPsi_level_one_bound K
  obtain ⟨C₂, hC₂, hrest⟩ :=
    norm_adjustedTwistedPsi_smallConductor_bound hzf K R hR
  let C : ℝ := C₁ + C₂
  have hC : 0 < C := by dsimp only [C]; exact add_pos hC₁ hC₂
  refine ⟨C, hC, ?_⟩
  filter_upwards [hone, hrest,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop 0)] with x hone hrest hlog
  intro H hH
  let M : ℝ := C * (x : ℝ) / Real.log (x : ℝ) ^ K
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hmean := primitiveAdjustedMean_le_mul_of_character_bound x H M hM
    (fun q _ χ hqH hχ => by
      by_cases hq1 : q = 1
      · subst q
        exact (hone χ).trans (by
          calc
            C₁ * (x : ℝ) / Real.log (x : ℝ) ^ K =
                C₁ * ((x : ℝ) / Real.log (x : ℝ) ^ K) := by ring
            _ ≤ C * ((x : ℝ) / Real.log (x : ℝ) ^ K) :=
              mul_le_mul_of_nonneg_right
                (show C₁ ≤ C by dsimp only [C]; linarith) (by positivity)
            _ = C * (x : ℝ) / Real.log (x : ℝ) ^ K := by ring)
      · have hq2 : 2 ≤ q := by
          have : 0 < q := NeZero.pos q
          omega
        have hqR : (q : ℝ) ≤ Real.log (x : ℝ) ^ R := by
          exact (by exact_mod_cast hqH : (q : ℝ) ≤ (H : ℝ)).trans hH
        exact (hrest q χ hq2 hqR hχ).trans (by
          calc
            C₂ * (x : ℝ) / Real.log (x : ℝ) ^ K =
                C₂ * ((x : ℝ) / Real.log (x : ℝ) ^ K) := by ring
            _ ≤ C * ((x : ℝ) / Real.log (x : ℝ) ^ K) :=
              mul_le_mul_of_nonneg_right
                (show C₂ ≤ C by dsimp only [C]; linarith) (by positivity)
            _ = C * (x : ℝ) / Real.log (x : ℝ) ^ K := by ring))
  dsimp only [M] at hmean
  calc
    primitiveAdjustedMean x 0 H ≤
        (H : ℝ) * (C * (x : ℝ) / Real.log (x : ℝ) ^ K) := hmean
    _ = C * (H : ℝ) * (x : ℝ) /
        Real.log (x : ℝ) ^ K := by ring
end Chen.BombieriVinogradov

end

/-! ## SourceD22ThetaStrong -/

section

open Filter Topology Asymptotics Real
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- Preserve the full logarithmic accuracy of the already checked MediumPNT. -/
theorem sourceD22_theta_all_log_powers (A : ℝ) :
    (Chebyshev.theta-id) =o[atTop] (fun x : ℝ => x*(Real.log x)^(-A)) := by
  obtain ⟨c,hc,hpsi⟩ := MediumPNT
  have hpow : (fun x : ℝ => ((Real.log x)^((1:ℝ)/10))^(-10*A)) =ᶠ[atTop]
      (fun x => (Real.log x)^(-A)) := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    rw [←Real.rpow_mul (Real.log_nonneg hx)]
    congr 1; ring
  have hdecay : (fun x : ℝ => Real.exp (-c*(Real.log x)^((1:ℝ)/10))) =o[atTop]
      (fun x => (Real.log x)^(-A)) := by
    exact ((isLittleO_exp_neg_mul_rpow_atTop hc (-10*A)).comp_tendsto
      ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).comp Real.tendsto_log_atTop)).congr'
      (Eventually.of_forall fun _ => rfl) hpow
  have hmedium := (isBigO_refl (fun x : ℝ => x) atTop).mul_isLittleO hdecay
  have hpsi' : (Chebyshev.psi-id) =o[atTop] (fun x : ℝ => x*(Real.log x)^(-A)) :=
    hpsi.trans_isLittleO hmedium
  have hlogbase := isLittleO_log_rpow_rpow_atTop (s:=1/2) A (by norm_num)
  have hmul := (isBigO_refl Real.sqrt atTop).mul_isLittleO hlogbase
  have hsprod : (fun x : ℝ => Real.sqrt x*(Real.log x)^A) =o[atTop] id := by
    refine hmul.congr' (Eventually.of_forall fun _ => rfl) ?_
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    rw [←Real.sqrt_eq_rpow,←pow_two,Real.sq_sqrt hx]; rfl
  have hlog : ∀ᶠ x : ℝ in atTop, (Real.log x)^A≠0 := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    exact (Real.rpow_pos_of_pos (Real.log_pos hx) A).ne'
  have hsdiv := (isLittleO_mul_iff_isLittleO_div
    (f:=fun x : ℝ => (Real.log x)^A) (g:=Real.sqrt) (h:=id) hlog).mp
    (by simpa only [mul_comm] using hsprod)
  have hsqrt : Real.sqrt =o[atTop] (fun x : ℝ => x*(Real.log x)^(-A)) := by
    refine hsdiv.congr' (Eventually.of_forall fun _ => rfl) ?_
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    rw [Real.rpow_neg (Real.log_nonneg hx)]; rfl
  have hdelta := Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrt
  have heq : Chebyshev.theta-id = (Chebyshev.psi-id)-(Chebyshev.psi-Chebyshev.theta) := by
    funext x; simp only [Pi.sub_apply,id_eq]; ring
  rw [heq]
  exact hpsi'.sub hdelta

end Green64Analytic.SourceBlockSieve

end

/-! ## ExactPNT2 -/

section

open Filter Topology Asymptotics Real
open scoped Chebyshev
set_option maxHeartbeats 8000000
namespace Green64Analytic.SourceSimplexGeometry

theorem primeRemainder_isBigO_of_theta_error
    (hTheta : (Chebyshev.theta - id) =O[atTop]
        fun x : ℝ => x / Real.log x) :
    Green64Analytic.ReciprocalPrimeGrid.primeRemainder =O[atTop]
        (fun x : ℝ => x / (Real.log x)^2) := by
  have hscaled :
      (fun x : ℝ => (Chebyshev.theta x - x)/Real.log x) =O[atTop]
        (fun x : ℝ => x / (Real.log x)^2) := by
    have h := hTheta.mul
      (isBigO_refl (fun x : ℝ => (Real.log x)⁻¹) atTop)
    refine h.congr' ?_ ?_
    · exact Eventually.of_forall (fun x => by
        simp only [Pi.sub_apply, id_eq, div_eq_mul_inv])
    · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
      have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
      change (x / Real.log x) * (Real.log x)⁻¹ =
        x / (Real.log x)^2
      field_simp
  have hPiTheta := Chebyshev.primeCounting_sub_theta_div_log_isBigO
  have hSum := hPiTheta.add hscaled
  refine hSum.congr' ?_ (Eventually.of_forall fun _ => rfl)
  exact Eventually.of_forall fun x => by
    simp only [Green64Analytic.ReciprocalPrimeGrid.primeRemainder,
      Green64Analytic.ReciprocalPrimeGrid.primeCountReal_eq]
    ring

theorem pnt2_positive_constant_of_theta_error
    (hTheta : (Chebyshev.theta - id) =O[atTop]
        fun x : ℝ => x / Real.log x) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x : ℝ in atTop,
        |Green64Analytic.ReciprocalPrimeGrid.primeRemainder x| ≤
          C*x/(Real.log x)^2 := by
  have hbig := primeRemainder_isBigO_of_theta_error hTheta
  obtain ⟨C, hC⟩ := hbig.bound
  let K : ℝ := max |C| 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (2:ℝ)] with x hB hx
  have hG0 : 0 ≤ x/(Real.log x)^2 := by positivity
  have hCK : C ≤ K := (le_abs_self C).trans (le_max_left _ _)
  have hNorm : ‖x/(Real.log x)^2‖ = x/(Real.log x)^2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hG0]
  have hBound : |Green64Analytic.ReciprocalPrimeGrid.primeRemainder x| ≤
      K * (x/(Real.log x)^2) := by
    calc
      _ = ‖Green64Analytic.ReciprocalPrimeGrid.primeRemainder x‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ C * ‖x/(Real.log x)^2‖ := hB
      _ = C * (x/(Real.log x)^2) := by rw [hNorm]
      _ ≤ K * (x/(Real.log x)^2) :=
        mul_le_mul_of_nonneg_right hCK hG0
  simpa only [mul_div_assoc] using hBound

theorem pnt2_L_of_theta_error
    (b : ℝ) (hb : 0 < b)
    (hTheta : (Chebyshev.theta - id) =O[atTop]
        fun x : ℝ => x / Real.log x) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ᶠ L : ℝ in atTop,
        ∀ t, Real.exp (b*L) ≤ t →
          |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t| ≤
            C*t/(Real.log t)^2) := by
  obtain ⟨C, hC, hBound⟩ :=
    pnt2_positive_constant_of_theta_error hTheta
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hBound
  have hLinear : Tendsto (fun L : ℝ => b*L) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    filter_upwards [eventually_ge_atTop (M/b)] with L hL
    have hmul := mul_le_mul_of_nonneg_left hL hb.le
    have hcancel : b*(M/b) = M := mul_div_cancel₀ M hb.ne'
    linarith
  have hExp : Tendsto (fun L : ℝ => Real.exp (b*L))
      atTop atTop := Real.tendsto_exp_atTop.comp hLinear
  have hThreshold : ∀ᶠ L : ℝ in atTop,
      T ≤ Real.exp (b*L) :=
    hExp.eventually (eventually_ge_atTop T)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hThreshold] with L hL
  intro t ht
  exact hT t (hL.trans ht)

end Green64Analytic.SourceSimplexGeometry
namespace Green64Analytic.SourcePNT2

theorem source_pnt2_unconditional
    (b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ L : ℝ in atTop,
        ∀ t, exp (b*L) ≤ t →
          |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t| ≤
            C*t/(log t)^2 := by
  have hTheta : (Chebyshev.theta - id) =O[atTop]
      (fun x : ℝ => x / Real.log x) := by
    simpa only [Real.rpow_neg_one, div_eq_mul_inv] using
      (Green64Analytic.SourceBlockSieve.sourceD22_theta_all_log_powers (1 : ℝ)).isBigO
  exact Green64Analytic.SourceSimplexGeometry.pnt2_L_of_theta_error b hb hTheta


end Green64Analytic.SourcePNT2

end

/-! ## SourceD22ThetaUniform -/

section

open Filter Topology Asymptotics
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- Arbitrary log-power precision uniformly above a positive power of exp L. -/
theorem sourceD22_theta_uniform (β A ε : ℝ) (hβ : 0<β) (hA : 0<A) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ t : ℝ, Real.exp (β*L)≤t →
      |Chebyshev.theta t-t|≤ε*t*L^(-A) := by
  have hbound := (sourceD22_theta_all_log_powers A).bound
    (show 0<ε*β^A by positivity)
  obtain ⟨T,hT⟩ := eventually_atTop.mp hbound
  have hscale := ((tendsto_rpow_atTop hβ).comp Real.tendsto_exp_atTop).eventually_ge_atTop T
  filter_upwards [hscale,eventually_gt_atTop (0:ℝ)] with L hs hL
  intro t ht
  have he : (Real.exp L)^β=Real.exp (β*L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,mul_comm]
  have ht0 : 0<t := (Real.exp_pos _).trans_le ht
  have ht1 : 1<t := (Real.one_lt_exp_iff.mpr (mul_pos hβ hL)).trans_le ht
  have hlog : β*L≤Real.log t := by
    have h := Real.log_le_log (Real.exp_pos _) ht
    simpa only [Real.log_exp] using h
  have hp : 0≤t*(Real.log t)^(-A) := mul_nonneg ht0.le (Real.rpow_nonneg (Real.log_pos ht1).le _)
  have hTL : T≤Real.exp (β*L) := by simpa only [Function.comp_def,he] using hs
  have hb := hT t (hTL.trans ht)
  simp only [Pi.sub_apply,id_eq,Real.norm_eq_abs,abs_of_nonneg hp] at hb
  have hpow : (Real.log t)^(-A)≤β^(-A)*L^(-A) := by
    have hh := Real.rpow_le_rpow_of_nonpos (mul_pos hβ hL) hlog (show -A≤(0:ℝ) by linarith)
    simpa only [Real.mul_rpow hβ.le hL.le] using hh
  calc
    _ ≤ (ε*β^A)*(t*(Real.log t)^(-A)) := hb
    _ ≤ (ε*β^A)*(t*(β^(-A)*L^(-A))) := by gcongr
    _ = _ := by
      have hc : β^A*β^(-A)=1 := by rw [←Real.rpow_add hβ]; simp
      calc
        _ = ε*t*L^(-A)*(β^A*β^(-A)) := by ring
        _ = _ := by rw [hc,mul_one]

end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD22ThetaCell -/

section

open Filter Topology
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- Sharp theta increment on the actual L^-S cells, uniformly for all Y>=exp(beta L). -/
theorem sourceD22_theta_cell_relative (S β ε : ℝ) (hS : 0<S) (hβ : 0<β) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, Real.exp (β*L)≤Y →
      let Δ := L^(-S)
      let H := (Real.exp Δ-1)*Y
      |Chebyshev.theta (Real.exp Δ*Y)-Chebyshev.theta Y-H|≤ε*H := by
  let c := ε/(Real.exp 1+1)
  have hc : 0<c := by dsimp [c]; positivity
  filter_upwards [sourceD22_theta_uniform β S c hβ hS hc,eventually_ge_atTop (1:ℝ)] with L ht hL
  intro Y hY
  let Δ := L^(-S)
  let Z := Real.exp Δ*Y
  let H := (Real.exp Δ-1)*Y
  have hΔ : 0<Δ := Real.rpow_pos_of_pos (by linarith) _
  have hYpos : 0<Y := (Real.exp_pos _).trans_le hY
  have hmesh : Δ≤1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL (show -S≤0 by linarith)
  have hZY : Y≤Z := le_mul_of_one_le_left hYpos.le (Real.one_le_exp hΔ.le)
  have heY := ht Y hY
  have heZ := ht Z (hY.trans hZY)
  have heq : Chebyshev.theta Z-Chebyshev.theta Y-H =
      (Chebyshev.theta Z-Z)-(Chebyshev.theta Y-Y) := by dsimp [Z,H]; ring
  have hsum := (abs_sub (Chebyshev.theta Z-Z) (Chebyshev.theta Y-Y)).trans (add_le_add heZ heY)
  have hZup : Z≤Real.exp 1*Y := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hmesh) hYpos.le
  have hmain : Δ*Y≤H := mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp Δ]) hYpos.le
  have hcanc : c*(Real.exp 1+1)=ε := by dsimp [c]; field_simp
  have hbound : c*Z*Δ+c*Y*Δ≤ε*(Δ*Y) := by
    calc
      _ = (c*Δ)*(Z+Y) := by ring
      _ ≤ (c*Δ)*((Real.exp 1+1)*Y) := mul_le_mul_of_nonneg_left (by nlinarith [hZup]) (mul_nonneg hc.le hΔ.le)
      _ = (c*(Real.exp 1+1))*(Δ*Y) := by ring
      _ = _ := by rw [hcanc]
  change |Chebyshev.theta Z-Chebyshev.theta Y-H|≤ε*H
  rw [heq]
  exact (hsum.trans hbound).trans (mul_le_mul_of_nonneg_left hmain hε.le)

/-- Sharp upper numerator in the prime-only regime and an input for the full rough-density recurrence. -/
theorem sourceD22_prime_cell_upper (S β ε : ℝ) (hS : 0<S) (hβ : 0<β) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, Real.exp (β*L)≤Y →
      sourceD22PrimeCount Y (L^(-S)) ≤ (1+ε)*(Real.exp (L^(-S))-1)*Y/Real.log Y := by
  filter_upwards [sourceD22_theta_cell_relative S β ε hS hβ hε,eventually_gt_atTop (0:ℝ)] with L ht hL
  intro Y hY
  have hY1 : 1<Y := (Real.one_lt_exp_iff.mpr (mul_pos hβ hL)).trans_le hY
  have hc := sourceD22_prime_count_theta_upper Y (L^(-S)) hY1 (Real.rpow_nonneg hL.le _)
  have he := (abs_le.mp (ht Y hY)).2
  apply (le_div_iff₀ (Real.log_pos hY1)).mpr
  nlinarith only [hc,he]


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD22PrimeOnlyNumerator -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- True rough integers below y^2 must be prime; repeated prime factors are not omitted. -/
theorem sourceD22_rough_count_le_prime (Y Δ y : ℝ) (hY : 0 ≤ Y) (hy : 0 ≤ y)
    (hupper : Real.exp Δ*Y ≤ y^2) :
    sourceD22Count Y Δ y ≤ sourceD22PrimeCount Y Δ := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hcell,hr⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hcell,?_⟩
  by_contra hnp
  have hn0 : 0<n := by have := hr.1; omega
  have hsq : (n.minFac:ℝ)^2 ≤ n := by exact_mod_cast Nat.minFac_sq_le_self hn0 hnp
  have hnY : (n:ℝ) ≤ Real.exp Δ*Y :=
    (Nat.cast_le.mpr (Finset.mem_Ioc.mp hcell).2).trans
      (Nat.floor_le (mul_nonneg (Real.exp_pos _).le hY))
  have hrY : y<(n.minFac:ℝ) := hr.2
  nlinarith

/-- Sharp numerator for every full cell below the genuine two-prime threshold. -/
theorem sourceD22_prime_only_numerator (S β ε : ℝ) (hS : 0<S) (hβ : 0<β) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ Y y : ℝ, Real.exp (β*L)≤Y → 0≤y →
      Real.exp (L^(-S))*Y≤y^2 →
      sourceD22Count Y (L^(-S)) y ≤ (1+ε)*(Real.exp (L^(-S))-1)*Y/Real.log Y := by
  filter_upwards [sourceD22_prime_cell_upper S β ε hS hβ hε] with L hL
  intro Y y hY hy hupper
  exact (sourceD22_rough_count_le_prime Y (L^(-S)) y
    ((Real.exp_pos _).le.trans hY) hy hupper).trans (hL Y hY)

lemma sourceD22_two_prime_threshold (S γ σ : ℝ) (hS : 0<S) (hgap : σ<2*γ) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, Y≤Real.exp (σ*L) →
      Real.exp (L^(-S))*Y≤((Real.exp L)^γ)^2 := by
  filter_upwards [eventually_ge_atTop (max 1 (1/(2*γ-σ)))] with L hL
  have hL1 : 1≤L := (le_max_left _ _).trans hL
  have hLH : 1/(2*γ-σ)≤L := (le_max_right _ _).trans hL
  have hpow : L^(-S)≤1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1 (show -S≤0 by linarith)
  have hh : 1≤L*(2*γ-σ) := (div_le_iff₀ (by linarith)).mp hLH
  intro Y hY
  calc
    _ ≤ Real.exp (L^(-S))*Real.exp (σ*L) := mul_le_mul_of_nonneg_left hY (Real.exp_pos _).le
    _ = Real.exp (L^(-S)+σ*L) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (2*γ*L) := Real.exp_le_exp.mpr (by nlinarith only [hh,hpow])
    _ = _ := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,←Real.exp_nat_mul]
      congr 1; push_cast; ring


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD23SemiprimeFibre -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

noncomputable def sourceD23SmallPrimes (Y Δ y : ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.exp Δ*Y⌋₊+1)).filter
    (fun p => p.Prime ∧ y<(p:ℝ) ∧ (p:ℝ)^2≤Real.exp Δ*Y)
noncomputable def sourceD23CompositeSet (Y Δ y : ℝ) : Finset ℕ :=
  (sourceD22Cell Y Δ).filter (fun n => sourceD20Rough y n ∧ ¬n.Prime)

/-- Exact prime fibre after dividing a genuine full cell. -/
lemma sourceD23_divided_cell (Y Δ : ℝ) (p n : ℕ) (hp : 0<p)
    (hn : n∈sourceD22Cell Y Δ) (hpn : p∣n) (hY : 0≤Y) :
    n/p ∈ sourceD22Cell (Y/(p:ℝ)) Δ := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hprod : p*(n/p)=n := Nat.mul_div_cancel' hpn
  have hlo : Y<(n:ℝ) := (Nat.floor_lt hY).mp (Finset.mem_Ioc.mp hn).1
  have hhi : (n:ℝ)≤Real.exp Δ*Y :=
    (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans
      (Nat.floor_le (mul_nonneg (Real.exp_pos _).le hY))
  have he : (p:ℝ)*((n/p:ℕ):ℝ)=n := by exact_mod_cast hprod
  apply Finset.mem_Ioc.mpr
  constructor
  · apply (Nat.floor_lt (div_nonneg hY hpR.le)).mpr
    apply (div_lt_iff₀ hpR).mpr
    nlinarith only [he,hlo]
  · apply Nat.le_floor
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hpR).mpr
    nlinarith only [he,hhi]

/-- Every composite in the first mixed stratum has its actual prime cofactor.
No coprimality or squarefree condition is imposed. -/
theorem sourceD23_composite_fibre (Y Δ y : ℝ) (hY : 0≤Y) (hy : 0≤y)
    (hthree : Real.exp Δ*Y≤y^3) (n : ℕ)
    (hn : n∈sourceD23CompositeSet Y Δ y) :
    n.minFac∈sourceD23SmallPrimes Y Δ y ∧
    n/n.minFac∈(sourceD22Cell (Y/(n.minFac:ℝ)) Δ).filter Nat.Prime := by
  obtain ⟨hcell,hr,hnp⟩ := Finset.mem_filter.mp hn
  have hp : n.minFac.Prime := Nat.minFac_prime (by have := hr.1; omega)
  have hn0 : 0<n := by have := hr.1; omega
  have hnZ : (n:ℝ)≤Real.exp Δ*Y :=
    (Nat.cast_le.mpr (Finset.mem_Ioc.mp hcell).2).trans
      (Nat.floor_le (mul_nonneg (Real.exp_pos _).le hY))
  have hcR : (n:ℝ)<(n.minFac:ℝ)^3 :=
    (hnZ.trans hthree).trans_lt (pow_lt_pow_left₀ hr.2 hy (by norm_num))
  have hcube : n<n.minFac^3 := by exact_mod_cast hcR
  have hq := source_composite_cofactor_prime_of_minfac_cube_gt hr.1 hnp hcube
  have hpN := (Nat.minFac_le hn0).trans (Finset.mem_Ioc.mp hcell).2
  have hpSq : (n.minFac:ℝ)^2≤n := by exact_mod_cast Nat.minFac_sq_le_self hn0 hnp
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp,hr.2,hpSq.trans hnZ⟩,?_⟩
  exact Finset.mem_filter.mpr ⟨sourceD23_divided_cell Y Δ n.minFac n hp.pos hcell
    (Nat.minFac_dvd n) hY,hq⟩

end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD23MixedCount -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- An injective smallest-prime cover counts p^2 once, not twice. -/
theorem sourceD23_composite_count_upper (Y Δ y : ℝ) (hY : 0≤Y) (hy : 0≤y)
    (hthree : Real.exp Δ*Y≤y^3) :
    ((sourceD23CompositeSet Y Δ y).card:ℝ) ≤
      ∑ p∈sourceD23SmallPrimes Y Δ y,sourceD22PrimeCount (Y/(p:ℝ)) Δ := by
  let S := sourceD23CompositeSet Y Δ y
  let T := (sourceD23SmallPrimes Y Δ y).sigma
    (fun p => (sourceD22Cell (Y/(p:ℝ)) Δ).filter Nat.Prime)
  let f : ℕ → (Σ _p : ℕ,ℕ) := fun n => ⟨n.minFac,n/n.minFac⟩
  have hmap : Set.MapsTo f (↑S) (↑T) := by
    intro n hn
    exact Finset.mem_sigma.mpr (sourceD23_composite_fibre Y Δ y hY hy hthree n hn)
  have hinj : Set.InjOn f (↑S) := by
    intro n hn m hm he
    have hh := congrArg (fun z : (Σ _p : ℕ,ℕ) => z.1*z.2) he
    simpa only [f,Nat.mul_div_cancel' (Nat.minFac_dvd n),
      Nat.mul_div_cancel' (Nat.minFac_dvd m)] using hh
  have hcard := Finset.card_le_card_of_injOn f hmap hinj
  have hreal : (S.card:ℝ)≤(T.card:ℝ) := by exact_mod_cast hcard
  simpa only [T,Finset.card_sigma,Nat.cast_sum,sourceD22PrimeCount] using hreal

/-- Genuine rough count in the first mixed stratum: prime term plus exact
smallest-prime/cofactor cells, including all repeated factors. -/
theorem sourceD23_mixed_count_upper (Y Δ y : ℝ) (hY : 0≤Y) (hy : 0≤y)
    (hthree : Real.exp Δ*Y≤y^3) :
    sourceD22Count Y Δ y ≤ sourceD22PrimeCount Y Δ +
      ∑ p∈sourceD23SmallPrimes Y Δ y,sourceD22PrimeCount (Y/(p:ℝ)) Δ := by
  let C := (sourceD22Cell Y Δ).filter (sourceD20Rough y)
  have hsplit := Finset.card_filter_add_card_filter_not (s:=C) (p:=Nat.Prime)
  have hsub : C.filter Nat.Prime ⊆ (sourceD22Cell Y Δ).filter Nat.Prime := by
    intro n hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1,
      (Finset.mem_filter.mp hn).2⟩
  have he : C.filter (fun n => ¬n.Prime)=sourceD23CompositeSet Y Δ y := by
    ext n; simp only [C,sourceD23CompositeSet,Finset.mem_filter]; tauto
  have hc := Nat.cast_le (α:=ℝ) |>.mpr (Finset.card_le_card hsub)
  have hce := sourceD23_composite_count_upper Y Δ y hY hy hthree
  rw [he] at hsplit
  have hr : ((C.filter Nat.Prime).card:ℝ)+((sourceD23CompositeSet Y Δ y).card:ℝ)
      = sourceD22Count Y Δ y := by
    change ((C.filter Nat.Prime).card:ℝ)+((sourceD23CompositeSet Y Δ y).card:ℝ) = (C.card:ℝ)
    exact_mod_cast hsplit
  change ((C.filter Nat.Prime).card:ℝ) ≤ sourceD22PrimeCount Y Δ at hc
  linarith


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceNativeQuantitativePNT -/

section

set_option maxHeartbeats 4400000
open Filter Topology Asymptotics Real
open scoped Chebyshev
namespace Green64Analytic.SourceSimplexGeometry

/-- Converts the exact medium-PNT Chebyshev theta bound into the
PNT2 prime-counting remainder needed by the genuine SmallB source
grid. The theta bound is an explicit dependency, never an axiom. -/
theorem primeRemainder_isBigO_of_theta_error_from_medium_pnt
    (hTheta : (Chebyshev.theta - id) =O[atTop]
        fun x : ℝ => x / Real.log x) :
    Green64Analytic.ReciprocalPrimeGrid.primeRemainder =O[atTop]
        (fun x : ℝ => x / (Real.log x)^2) := by
  have hscaled :
      (fun x : ℝ => (Chebyshev.theta x - x)/Real.log x) =O[atTop]
        (fun x : ℝ => x / (Real.log x)^2) := by
    have h := hTheta.mul
      (isBigO_refl (fun x : ℝ => (Real.log x)⁻¹) atTop)
    refine h.congr' ?_ ?_
    · exact Eventually.of_forall (fun x => by
        simp only [Pi.sub_apply, id_eq, div_eq_mul_inv])
    · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
      have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
      change (x / Real.log x) * (Real.log x)⁻¹ =
        x / (Real.log x)^2
      field_simp
  have hPiTheta := Chebyshev.primeCounting_sub_theta_div_log_isBigO
  have hSum := hPiTheta.add hscaled
  refine hSum.congr' ?_ (Eventually.of_forall fun _ => rfl)
  exact Eventually.of_forall fun x => by
    simp only [Pi.add_apply, Green64Analytic.ReciprocalPrimeGrid.primeRemainder,
      Green64Analytic.ReciprocalPrimeGrid.primeCountReal_eq]
    ring

end Green64Analytic.SourceSimplexGeometry

namespace Green64Analytic.SourceSimplexGeometry

/-- Extract an eventual positive constant from the genuine Mathlib
prime-counting big-O consequence of the theta error. -/
theorem pnt2_positive_constant_of_theta_error_from_medium_pnt
    (hTheta : (Chebyshev.theta - id) =O[atTop]
        fun x : ℝ => x / Real.log x) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x : ℝ in atTop,
        |Green64Analytic.ReciprocalPrimeGrid.primeRemainder x| ≤
          C*x/(Real.log x)^2 := by
  have hbig := primeRemainder_isBigO_of_theta_error_from_medium_pnt hTheta
  obtain ⟨C, hC⟩ := hbig.bound
  let K : ℝ := max |C| 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (2:ℝ)] with x hB hx
  have hG0 : 0 ≤ x/(Real.log x)^2 := by positivity
  have hCK : C ≤ K := (le_abs_self C).trans (le_max_left _ _)
  have hNorm : ‖x/(Real.log x)^2‖ = x/(Real.log x)^2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hG0]
  have hBound : |Green64Analytic.ReciprocalPrimeGrid.primeRemainder x| ≤
      K * (x/(Real.log x)^2) := by
    calc
      _ = ‖Green64Analytic.ReciprocalPrimeGrid.primeRemainder x‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ C * ‖x/(Real.log x)^2‖ := hB
      _ = C * (x/(Real.log x)^2) := by rw [hNorm]
      _ ≤ K * (x/(Real.log x)^2) :=
        mul_le_mul_of_nonneg_right hCK hG0
  simpa only [mul_div_assoc] using hBound

/-- An unconditional-in-L lower threshold follows from a global
classical theta error, with exactly the PNT2' quantifiers used by
the source rough-count comparison. -/
theorem pnt2_L_of_theta_error_from_medium_pnt
    (b : ℝ) (hb : 0 < b)
    (hTheta : (Chebyshev.theta - id) =O[atTop]
        fun x : ℝ => x / Real.log x) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ᶠ L : ℝ in atTop,
        ∀ t, Real.exp (b*L) ≤ t →
          |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t| ≤
            C*t/(Real.log t)^2) := by
  obtain ⟨C, hC, hBound⟩ :=
    pnt2_positive_constant_of_theta_error_from_medium_pnt hTheta
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hBound
  have hLinear : Tendsto (fun L : ℝ => b*L) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    filter_upwards [eventually_ge_atTop (M/b)] with L hL
    have hmul := mul_le_mul_of_nonneg_left hL hb.le
    have hcancel : b*(M/b) = M := mul_div_cancel₀ M hb.ne'
    linarith
  have hExp : Tendsto (fun L : ℝ => Real.exp (b*L))
      atTop atTop := Real.tendsto_exp_atTop.comp hLinear
  have hThreshold : ∀ᶠ L : ℝ in atTop,
      T ≤ Real.exp (b*L) :=
    hExp.eventually (eventually_ge_atTop T)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hThreshold] with L hL
  intro t ht
  exact hT t (hL.trans ht)

end Green64Analytic.SourceSimplexGeometry
namespace Green64Analytic.SourcePNT2

/-- Pinned adaptation of PrimeNumberTheoremAnd.Consequences.isLittleO_sqrt_mul_log
in subfish-zhou/goldbach-lean@09b97db5, from Mathlib's
isLittleO_log_rpow_atTop without importing the PNTAnd source module. -/
theorem sqrt_mul_log_isLittleO_id :
    (fun x : ℝ => x.sqrt * x.log) =o[atTop] id := by
  have h : (fun x : ℝ => x.sqrt * x.log) =o[atTop]
      (fun x => x) := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert! isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
        using 2 with x
      rw [div_sqrt, sqrt_eq_rpow]
  exact h

/-- Source-attributed adaptation of the quantitative theta argument
in subfish-zhou/goldbach-lean@09b97db5,
AnalyticNumberTheory/PrimeDistribution/ChebyshevTheta.lean.
The medium psi PNT remains an explicit premise, not an axiom. -/
theorem theta_error_of_medium_psi
    (hMedium : ∃ c : ℝ, 0 < c ∧
       (Chebyshev.psi - id) =O[atTop]
          (fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10)))) :
    (Chebyshev.theta - id) =O[atTop]
       (fun x : ℝ => x / log x) := by
  obtain ⟨c, hc, hpsi⟩ := hMedium
  have hlog : ∀ᶠ x : ℝ in atTop, log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (Real.log_pos hx).ne'
  have hsqrt : sqrt =o[atTop] fun x : ℝ => x / log x := by
    apply (isLittleO_mul_iff_isLittleO_div
      (f := log) (g := sqrt) (h := id) hlog).mp
    simpa [mul_comm] using sqrt_mul_log_isLittleO_id
  have hpow :
      (fun x : ℝ => (log x ^ ((1 : ℝ) / 10)) ^ (-10 : ℝ))
        =ᶠ[atTop] fun x => log x ^ (-1 : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [← Real.rpow_mul (Real.log_nonneg hx)]
    norm_num
  have hdecay :
      (fun x : ℝ => exp (-c * log x ^ ((1 : ℝ) / 10)))
        =o[atTop] fun x => log x ^ (-1 : ℝ) := by
    exact
      ((isLittleO_exp_neg_mul_rpow_atTop hc (-10)).comp_tendsto
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
          tendsto_log_atTop)).congr'
        (Eventually.of_forall fun _ => rfl) hpow
  have hmedium :
      (fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10)))
        =o[atTop] fun x => x / log x := by
    simpa [Real.rpow_neg_one, div_eq_mul_inv] using
      (isBigO_refl id atTop).mul_isLittleO hdecay
  have hpsi' :
      (Chebyshev.psi - id) =O[atTop] fun x : ℝ => x / log x :=
    hpsi.trans hmedium.isBigO
  have hdelta : (Chebyshev.psi - Chebyshev.theta) =O[atTop]
      fun x : ℝ => x / log x :=
    Chebyshev.isBigO_psi_sub_theta_sqrt.trans hsqrt.isBigO
  calc
    Chebyshev.theta - id =
        (Chebyshev.psi - id) - (Chebyshev.psi - Chebyshev.theta) := by
      funext x
      simp only [Pi.sub_apply, id_eq]
      ring
    _ =O[atTop] fun x : ℝ => x / log x := hpsi'.sub hdelta

end Green64Analytic.SourcePNT2

namespace Green64Analytic.SourcePNT2

/-- Unconditional quantitative PNT2' in precisely the source
prime-counting remainder and exact logarithmic cutoff variables.
PNTAnd.MediumPNT was independently replayed in pinned Lean 4.32.0,
with only propext, Classical.choice and Quot.sound. -/
theorem source_pnt2_unconditional_from_medium_pnt
    (b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ L : ℝ in atTop,
        ∀ t, exp (b*L) ≤ t →
          |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t| ≤
            C*t/(log t)^2 :=
  Green64Analytic.SourceSimplexGeometry.pnt2_L_of_theta_error_from_medium_pnt
    b hb (theta_error_of_medium_psi MediumPNT)

end Green64Analytic.SourcePNT2

end

/-! ## SourceNativeSmallConductorAudit -/

section

open Filter Real
open scoped Classical

namespace Green64Analytic.SourceSW

/-- No SW assumption: the native primitive mixed region is unconditional. -/
theorem norm_twistedPsi_smallConductor_unconditional
    (K R : ℕ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        2 ≤ q → (q : ℝ) ≤ Real.log (x : ℝ) ^ R →
          χ.IsPrimitive →
          ‖Chen.BombieriVinogradov.twistedPsi x χ‖ ≤
            C * (x : ℝ) / Real.log (x : ℝ) ^ K :=
  Chen.BombieriVinogradov.norm_twistedPsi_smallConductor_bound
    Chen.primitive_zero_free_region K R hR

end Green64Analytic.SourceSW

end

/-! ## SourceSaltKusmin -/

section

/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The Kusmin–Landau inequality and van der Corput's second-derivative test

This file develops the B-side foundation of the van der Corput exponential-sum
toolkit: the **Kusmin–Landau inequality** (`kusmin_landau`) and the discrete
**second-derivative test** (`vdC_second_derivative`, milestone 2).

## House note on the character

A concurrent executor is building `Salt/ExpSum/Basic.lean` with an additive
character `eR (x : ℝ) : ℂ := Complex.exp (2πi x)` and its API.  To stay
independent this file defines a **private local copy** `eK` with the *same*
definition.  The house should **unify `eK` with `eR` at wire-in** — every use
of `eK` here is exactly `Complex.exp (2 * π * x * I)`.

## Milestone 1 — Kusmin–Landau

Stated discretely on the consecutive differences `g n := f (n+1) - f n`.

**Mathematical note (a real catch).**  The naive discrete hypothesis
"`Int.fract (g n) ∈ [δ, 1-δ]` and `g` monotone" is *insufficient*: without
pinning `g n` into a *single* unit interval the bound degrades to
`O((b-a)/δ)` (each integer that `g` crosses between samples costs `≍ 1/δ` of
total variation).  In the continuous Kusmin–Landau this cannot happen —
continuity + monotonicity + "bounded away from integers" force `g` to stay in
one interval `(m+δ, m+1-δ)`.  We therefore state the honest discrete shadow:
there is a fixed integer `m` with `g n ∈ [m+δ, m+1-δ]` throughout.  This is
exactly the window that milestone 2's decomposition produces, so the two
milestones are internally consistent.

Result: `‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 1 / δ`  (absolute constant `C = 1`).

The engine is the telescoping weight `w n := (1 - eK (g n))⁻¹`.  Its key
feature (`wK_re`) is that `Re (w n) = 1/2` is *constant*, so the Abel
differences `w (n+1) - w n` are purely imaginary and their total variation
telescopes through `Im (w n) = cot(π · g n)/2`, which is monotone because `g`
is monotone.
-/

namespace Salt.ExpSum

open Real Finset

/-- Private local additive character `eK x = exp(2πi x)`.  **Unify with
`Basic.eR` at wire-in** (identical definition). -/
noncomputable def eK (x : ℝ) : ℂ := Complex.exp (((2 * π * x : ℝ) : ℂ) * Complex.I)

@[simp] lemma eK_norm (x : ℝ) : ‖eK x‖ = 1 := by
  simp only [eK]
  exact Complex.norm_exp_ofReal_mul_I _

lemma eK_add (x y : ℝ) : eK (x + y) = eK x * eK y := by
  simp only [eK, ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- Periodicity: `eK` is unchanged by adding an integer. -/
lemma eK_add_intCast (x : ℝ) (k : ℤ) : eK (x + (k : ℝ)) = eK x := by
  have h : (((2 * π * (x + (k : ℝ))) : ℝ) : ℂ) * Complex.I
      = (((2 * π * x : ℝ)) : ℂ) * Complex.I + (k : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast; ring
  simp only [eK, h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `eK` in real cos/sin form. -/
lemma eK_eq (s : ℝ) :
    eK s = (Real.cos (2 * π * s) : ℂ) + (Real.sin (2 * π * s) : ℂ) * Complex.I := by
  simp only [eK, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

lemma eK_re (s : ℝ) : (eK s).re = Real.cos (2 * π * s) := by
  rw [eK_eq]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

lemma eK_im (s : ℝ) : (eK s).im = Real.sin (2 * π * s) := by
  rw [eK_eq]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]

lemma one_sub_eK_re (s : ℝ) : (1 - eK s).re = 2 * Real.sin (π * s) ^ 2 := by
  have h1 : (1 - eK s).re = 1 - Real.cos (2 * π * s) := by simp [eK_re]
  rw [h1, show (2 : ℝ) * π * s = 2 * (π * s) by ring, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (π * s)]

lemma one_sub_eK_im (s : ℝ) : (1 - eK s).im = -(2 * Real.sin (π * s) * Real.cos (π * s)) := by
  have h1 : (1 - eK s).im = -Real.sin (2 * π * s) := by simp [eK_im]
  rw [h1, show (2 : ℝ) * π * s = 2 * (π * s) by ring, Real.sin_two_mul]

lemma normSq_one_sub_eK (s : ℝ) : Complex.normSq (1 - eK s) = 4 * Real.sin (π * s) ^ 2 := by
  rw [Complex.normSq_apply, one_sub_eK_re, one_sub_eK_im]
  nlinarith [Real.sin_sq_add_cos_sq (π * s)]

/-- Norm of `1 - eK s` as `2|sin(πs)|`. -/
lemma norm_one_sub_eK (s : ℝ) : ‖1 - eK s‖ = 2 * |Real.sin (π * s)| := by
  rw [Complex.norm_def, normSq_one_sub_eK]
  rw [show (4 : ℝ) * Real.sin (π * s) ^ 2 = (2 * |Real.sin (π * s)|) ^ 2 by
        rw [mul_pow]; rw [sq_abs]; ring]
  exact Real.sqrt_sq (by positivity)

/-- The telescoping weight. -/
noncomputable def wK (s : ℝ) : ℂ := (1 - eK s)⁻¹

/-- `Re (wK s) = 1/2` (constant!) whenever `sin(πs) ≠ 0`. -/
lemma wK_re (s : ℝ) (hs : Real.sin (π * s) ≠ 0) : (wK s).re = 1 / 2 := by
  rw [wK, Complex.inv_re, normSq_one_sub_eK, one_sub_eK_re]
  have : Real.sin (π * s) ^ 2 ≠ 0 := pow_ne_zero 2 hs
  field_simp
  ring

/-- `Im (wK s) = cos(πs)/(2 sin(πs)) = cot(πs)/2`. -/
lemma wK_im (s : ℝ) (hs : Real.sin (π * s) ≠ 0) :
    (wK s).im = Real.cos (π * s) / (2 * Real.sin (π * s)) := by
  rw [wK, Complex.inv_im, normSq_one_sub_eK, one_sub_eK_im]
  field_simp
  ring

/-- `‖wK s‖ = 1 / (2|sin(πs)|)`. -/
lemma norm_wK (s : ℝ) : ‖wK s‖ = 1 / (2 * |Real.sin (π * s)|) := by
  rw [wK, norm_inv, norm_one_sub_eK, inv_eq_one_div]

/-- `sin(πs) > 0` for `s ∈ (0,1)`. -/
lemma sin_pi_mul_pos {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : 0 < Real.sin (π * s) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

/-- Jordan's inequality, symmetrised: `sin(πs) ≥ 2δ` for `s ∈ [δ, 1-δ]`, `δ ≤ 1/2`. -/
lemma sin_pi_mul_ge {δ s : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hs1 : δ ≤ s)
    (hs2 : s ≤ 1 - δ) : 2 * δ ≤ Real.sin (π * s) := by
  have hkey : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → 2 * t ≤ Real.sin (π * t) := by
    intro t ht0 ht1
    have hj := Real.mul_le_sin (x := π * t) (by positivity) (by nlinarith [Real.pi_pos])
    have hid : 2 / π * (π * t) = 2 * t := by field_simp
    linarith [hid ▸ hj]
  by_cases h : s ≤ 1 / 2
  · exact le_trans (by linarith) (hkey s (by linarith) h)
  · replace h := not_le.mp h
    have hsym : Real.sin (π * s) = Real.sin (π * (1 - s)) := by
      rw [show π * (1 - s) = π - π * s by ring, Real.sin_pi_sub]
    rw [hsym]
    exact le_trans (by linarith) (hkey (1 - s) (by linarith) (by linarith))

/-- Monotonicity of `Im (wK ·) = cot(π ·)/2`: antitone on `(0,1)`. -/
lemma wK_im_antitone {s₁ s₂ : ℝ} (h1 : 0 < s₁) (h12 : s₁ ≤ s₂) (h2 : s₂ < 1) :
    Real.cos (π * s₂) / (2 * Real.sin (π * s₂))
      ≤ Real.cos (π * s₁) / (2 * Real.sin (π * s₁)) := by
  have hs1 : 0 < Real.sin (π * s₁) := sin_pi_mul_pos h1 (lt_of_le_of_lt h12 h2)
  have hs2 : 0 < Real.sin (π * s₂) := sin_pi_mul_pos (lt_of_lt_of_le h1 h12) h2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsin : 0 ≤ Real.sin (π * s₂ - π * s₁) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos, mul_pos Real.pi_pos h1]
  rw [Real.sin_sub] at hsin
  nlinarith [hsin]

/-- A purely imaginary complex number has norm equal to `|Im|`. -/
lemma norm_eq_abs_im_of_re_eq_zero {z : ℂ} (h : z.re = 0) : ‖z‖ = |z.im| := by
  rw [Complex.norm_def, Complex.normSq_apply, h, zero_mul, zero_add, ← sq,
    Real.sqrt_sq_eq_abs]

/-- Abel summation over `range (N+1)`, telescoped form. -/
lemma abel_range (C B : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ range (N + 1), C k * (B k - B (k + 1))
      = C 0 * B 0 - C N * B (N + 1) + ∑ k ∈ range N, (C (k + 1) - C k) * B (k + 1) := by
  induction N with
  | zero => simp; ring
  | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]; ring

/-- **The Kusmin–Landau inequality (discrete form).**

Let `g n := f (n+1) - f n` be the consecutive differences of a phase `f`.
If `g` is monotone (increasing) on `(a, b]` and stays in a single unit
interval bounded away from the integers, `g n ∈ [m + δ, m + 1 - δ]` with
`δ ∈ (0, 1/2]`, then the exponential sum obeys
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 1 / δ`.  The constant is absolute (`C = 1`).

See the file header for why the single-interval hypothesis is essential
(the `Int.fract`-only form is genuinely too weak). -/
theorem kusmin_landau {f : ℕ → ℝ} {a b : ℕ} {δ : ℝ} {m : ℤ}
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hg_lb : ∀ n, a < n → n ≤ b → (m : ℝ) + δ ≤ f (n + 1) - f n)
    (hg_ub : ∀ n, a < n → n ≤ b → f (n + 1) - f n ≤ (m : ℝ) + 1 - δ)
    (hmono : ∀ n, a < n → n < b → f (n + 1) - f n ≤ f (n + 2) - f (n + 1)) :
    ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖ ≤ 1 / δ := by
  rcases Nat.lt_or_ge a b with hab | hab
  · -- Main case `a < b`.
    set N : ℕ := b - a - 1 with hNdef
    have hbN : b = a + 1 + N := by omega
    -- reindex `Ioc a b` to `range (N+1)`
    have hIoc : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hIoc, Finset.sum_Ico_eq_sum_range, show b + 1 - (a + 1) = N + 1 by omega]
    -- local sequences
    set σ : ℕ → ℝ := fun k => f (a + 1 + k + 1) - f (a + 1 + k) - (m : ℝ) with hσdef
    set B : ℕ → ℂ := fun k => eK (f (a + 1 + k)) with hBdef
    set W : ℕ → ℂ := fun k => wK (σ k) with hWdef
    -- range facts on `σ`
    have hσ_range : ∀ k, k ≤ N → δ ≤ σ k ∧ σ k ≤ 1 - δ := by
      intro k hk
      have h1 : a < a + 1 + k := by omega
      have h2 : a + 1 + k ≤ b := by omega
      have hlb := hg_lb (a + 1 + k) h1 h2
      have hub := hg_ub (a + 1 + k) h1 h2
      simp only [hσdef]; constructor <;> [linarith; linarith]
    have hsin_pos : ∀ k, k ≤ N → 0 < Real.sin (π * σ k) := by
      intro k hk
      obtain ⟨hl, hu⟩ := hσ_range k hk
      exact sin_pi_mul_pos (by linarith) (by linarith)
    have hsin_ge : ∀ k, k ≤ N → 2 * δ ≤ Real.sin (π * σ k) := by
      intro k hk
      obtain ⟨hl, hu⟩ := hσ_range k hk
      exact sin_pi_mul_ge hδ0 hδ hl hu
    have hσ_mono : ∀ k, k < N → σ k ≤ σ (k + 1) := by
      intro k hk
      have h1 : a < a + 1 + k := by omega
      have h2 : a + 1 + k < b := by omega
      have := hmono (a + 1 + k) h1 h2
      simp only [hσdef]
      have he : a + 1 + (k + 1) = a + 1 + k + 1 := by ring
      have he2 : a + 1 + k + 1 + 1 = a + 1 + k + 2 := by ring
      rw [he, he2]; linarith
    -- `Re W = 1/2`, `Im W = cot/2`, monotone, norm-bounded
    have hWre : ∀ k, k ≤ N → (W k).re = 1 / 2 := by
      intro k hk; simp only [hWdef]; exact wK_re _ (ne_of_gt (hsin_pos k hk))
    have hWim : ∀ k, k ≤ N →
        (W k).im = Real.cos (π * σ k) / (2 * Real.sin (π * σ k)) := by
      intro k hk; simp only [hWdef]; exact wK_im _ (ne_of_gt (hsin_pos k hk))
    have hWmono : ∀ k, k < N → (W (k + 1)).im ≤ (W k).im := by
      intro k hk
      rw [hWim (k + 1) (by omega), hWim k (by omega)]
      obtain ⟨hl, _⟩ := hσ_range k (by omega)
      obtain ⟨_, hu⟩ := hσ_range (k + 1) (by omega)
      exact wK_im_antitone (by linarith) (hσ_mono k hk) (by linarith)
    have hWimabs : ∀ k, k ≤ N → |(W k).im| ≤ 1 / (4 * δ) := by
      intro k hk
      have hs := hsin_pos k hk
      have hsg := hsin_ge k hk
      rw [hWim k hk, abs_div, abs_of_pos (mul_pos (by norm_num) hs)]
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hs) (by positivity)]
      have hcos : |Real.cos (π * σ k)| ≤ 1 := Real.abs_cos_le_one _
      nlinarith [hcos, hsg, hδ0,
        mul_le_mul_of_nonneg_right hcos (by positivity : (0 : ℝ) ≤ 4 * δ)]
    have hWnorm : ∀ k, k ≤ N → ‖W k‖ ≤ 1 / (4 * δ) := by
      intro k hk
      simp only [hWdef, norm_wK]
      have hs := hsin_pos k hk
      have hsg := hsin_ge k hk
      rw [abs_of_pos hs]
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    -- pointwise Kusmin–Landau identity
    have hid : ∀ k, k ≤ N → W k * (B k - B (k + 1)) = B k := by
      intro k hk
      have hne : 1 - eK (σ k) ≠ 0 := by
        intro hzero
        rw [← norm_eq_zero, norm_one_sub_eK] at hzero
        have hs := hsin_pos k hk
        have : |Real.sin (π * σ k)| = 0 := by linarith [abs_nonneg (Real.sin (π * σ k))]
        rw [abs_eq_zero] at this; linarith
      have hBrec : B (k + 1) = B k * eK (σ k) := by
        simp only [hBdef]
        rw [show f (a + 1 + (k + 1)) = f (a + 1 + k) + (σ k + (m : ℝ)) by
              simp only [hσdef]; ring]
        rw [eK_add, eK_add_intCast]
      rw [hBrec]
      have hfac : B k - B k * eK (σ k) = B k * (1 - eK (σ k)) := by ring
      rw [hfac]
      simp only [hWdef, wK]
      rw [mul_comm (B k) (1 - eK (σ k)), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    -- Abel + triangle inequality
    have hsumeq : ∑ k ∈ Finset.range (N + 1), B k
        = ∑ k ∈ Finset.range (N + 1), W k * (B k - B (k + 1)) :=
      Finset.sum_congr rfl fun k hk => (hid k (by simpa using Finset.mem_range.mp hk)).symm
    have hBnorm : ∀ k, ‖B k‖ = 1 := fun k => by simp only [hBdef]; exact eK_norm _
    rw [hsumeq, abel_range W B N]
    -- variation telescopes to `Im (W 0) - Im (W N)`
    have hvar : ∀ k, k < N → ‖W (k + 1) - W k‖ = (W k).im - (W (k + 1)).im := by
      intro k hk
      have hre : (W (k + 1) - W k).re = 0 := by
        rw [Complex.sub_re, hWre (k + 1) (by omega), hWre k (by omega)]; ring
      rw [norm_eq_abs_im_of_re_eq_zero hre, Complex.sub_im,
        abs_of_nonpos (by linarith [hWmono k hk])]; ring
    have hvarsum : ∑ k ∈ Finset.range N, ‖W (k + 1) - W k‖ = (W 0).im - (W N).im := by
      rw [Finset.sum_congr rfl fun k hk => hvar k (Finset.mem_range.mp hk)]
      exact Finset.sum_range_sub' (fun k => (W k).im) N
    calc ‖W 0 * B 0 - W N * B (N + 1)
              + ∑ k ∈ Finset.range N, (W (k + 1) - W k) * B (k + 1)‖
        ≤ ‖W 0 * B 0 - W N * B (N + 1)‖
            + ‖∑ k ∈ Finset.range N, (W (k + 1) - W k) * B (k + 1)‖ := norm_add_le _ _
      _ ≤ (‖W 0 * B 0‖ + ‖W N * B (N + 1)‖)
            + ∑ k ∈ Finset.range N, ‖(W (k + 1) - W k) * B (k + 1)‖ := by
          gcongr
          · exact norm_sub_le _ _
          · exact norm_sum_le _ _
      _ = (‖W 0‖ + ‖W N‖) + ∑ k ∈ Finset.range N, ‖W (k + 1) - W k‖ := by
          simp only [norm_mul, hBnorm, mul_one]
      _ = (‖W 0‖ + ‖W N‖) + ((W 0).im - (W N).im) := by rw [hvarsum]
      _ ≤ (1 / (4 * δ) + 1 / (4 * δ)) + (1 / (4 * δ) + 1 / (4 * δ)) := by
          gcongr
          · exact hWnorm 0 (by omega)
          · exact hWnorm N (by omega)
          · have h0 := le_trans (le_abs_self (W 0).im) (hWimabs 0 (by omega))
            have hN := le_trans (neg_le_abs (W N).im) (hWimabs N (by omega))
            linarith
      _ = 1 / δ := by field_simp; ring
  · -- Empty case `b ≤ a`.
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    positivity

/-!
## Milestone 2 — the second-derivative test (RESIDUAL; paper arithmetic recorded)

**Target statement.**  With `g n := f (n+1) - f n`, additionally assume the
second differences obey `λ ≤ g (n+1) - g n ≤ c · λ` for all `n` in range
(`0 < λ`, `1 ≤ c`).  Then, with `L := (b : ℝ) - a`,
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 5 · (c · L · √λ + 1 / √λ)`   (absolute `C' = 5`).

**Paper arithmetic (fully worked; this is the deliverable design).**

Set `δ := √λ`.  Split on the size of `λ`:

* **Case `λ > 1/4`** (so `√λ > 1/2`).  Bound trivially:
  `‖S‖ ≤ #(Ioc a b) = L` (each `‖eK‖ = 1`).  Since `c ≥ 1` and `√λ > 1/2`,
  `L < 2·c·L·√λ ≤ 5·(c L √λ + 1/√λ)`.  ✔

* **Case `λ ≤ 1/4`** (so `δ = √λ ≤ 1/2`, and `λ ≤ 1`).  Because
  `g (n+1) - g n ≥ λ > 0`, `g` is *strictly increasing*.  Decompose
  `Ioc a b` fibrewise by `k := ⌊g n⌋` (`Finset.sum_fiberwise_of_maps_to`):
  each fibre `F_k := {n ∈ Ioc a b : ⌊g n⌋ = k}` is contiparityus (`g` mono) and
  the fibres partition the range.  Within `F_k` split by monotonicity into

    - the **good part** `G_k := {n ∈ F_k : g n ∈ [k+δ, k+1-δ]}` — a single
      sub-`Ioc`, so `kusmin_landau` (with this `m := k`) gives
      `‖∑_{G_k} eK (f n)‖ ≤ 1/δ`;
    - the **bad part** `B_k := F_k \ G_k` = `{g n ∈ [k,k+δ) ∪ (k+1-δ,k+1)}`.
      Bound trivially by `#B_k`.  Since `g` increases by `≥ λ` per step, a
      window of `g`-length `w` holds `≤ w/λ + 1` indices, so each of the two
      bad sub-windows (length `δ`) has `≤ δ/λ + 1` indices:
      `#B_k ≤ 2·(δ/λ) + 2`.

  Number of non-empty fibres:
  `K ≤ ⌊g_b⌋ - ⌊g_{a+1}⌋ + 1 ≤ (g_b - g_{a+1}) + 1 ≤ c·λ·L + 1`.

  Summing over the `K` fibres:
  `‖S‖ ≤ K·(1/δ) + K·(2δ/λ + 2) = K·(1/δ + 2δ/λ + 2)`.
  With `δ = √λ`:  `1/δ = 1/√λ`, `2δ/λ = 2/√λ`, so the bracket is
  `3/√λ + 2`, and
  `‖S‖ ≤ (c λ L + 1)·(3/√λ + 2)`
       `= 3 c L √λ + 2 c λ L + 3/√λ + 2`.
  Using `λ ≤ 1` (`⇒ √λ ≤ 1`):  `2 c λ L = 2√λ·(c L √λ) ≤ 2 c L √λ` and
  `2 = 2√λ/√λ ≤ 2/√λ`.  Hence
  `‖S‖ ≤ 5 c L √λ + 5/√λ = 5·(c L √λ + 1/√λ)`.  ✔

Both cases give `C' = 5`.

**Why this is deferred (the real Lean cost).**  The elementary content above
needs three pieces of `Finset` engineering, the middle one being a genuine
sub-obstacle with no mathlib shortcut (see the recon: only the *identity*
predicate has `filter_lt_le_eq_Ioc`):

1.  fibrewise decomposition — available (`Finset.sum_fiberwise_of_maps_to`);
2.  **`G_k` (a monotone-predicate filter of an interval) equals an explicit
    `Finset.Ioc`** — must be built from `StrictMono (g)` by hand; this is a
    C-tier node in its own right and gates the `kusmin_landau` application;
3.  the crossing/window count `#B_k ≤ 2δ/λ + 2` and `K ≤ cλL + 1` from the
    per-step lower bound `g (n+1) - g n ≥ λ`.

`kusmin_landau` (milestone 1) is stated exactly to receive the good windows
`G_k` (single interval `m := k`, `g` increasing), so wiring is mechanical once
(2) lands.  Recorded as the named residual `VK-N2-M2` in `flags.md`.
-/

end Salt.ExpSum

end

/-! ## SourceLogDiscreteFirst -/

section

/-! The logarithmic increment window for the exact complete [U,4U] block.
The upstream Kusmin–Landau theorem consumes forward differences, not
pointwise values of the continuous derivative. -/
namespace Green64Analytic.CorrelationMellin

theorem source_log_increment_bounds (x : ℝ) (hx : 0 < x) :
    (x + 1)⁻¹ ≤ Real.log (x + 1) - Real.log x ∧
    Real.log (x + 1) - Real.log x ≤ x⁻¹ := by
  have hp : 0 < x + 1 := by linarith
  have h1 := Real.log_le_sub_one_of_pos (div_pos hp hx)
  have h2 := Real.log_le_sub_one_of_pos (div_pos hx hp)
  rw [Real.log_div (ne_of_gt hp) (ne_of_gt hx)] at h1
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hp)] at h2
  have hrat1 : (x + 1) / x - 1 = x⁻¹ := by
    field_simp
    ring
  have hrat2 : x / (x + 1) - 1 = -(x + 1)⁻¹ := by
    field_simp
    ring
  rw [hrat1] at h1
  rw [hrat2] at h2
  constructor <;> linarith
theorem source_log_increment_antitone (x y : ℝ)
    (hx : 0 < x) (hxy : x ≤ y) :
    Real.log (y + 1) - Real.log y ≤
      Real.log (x + 1) - Real.log x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hxp : 0 < x + 1 := by linarith
  have hyp : 0 < y + 1 := by linarith
  have hratio : (y + 1) / y ≤ (x + 1) / x := by
    rw [div_le_div_iff₀ hy hx]
    nlinarith
  have hlog := (Real.log_le_log_iff (div_pos hyp hy) (div_pos hxp hx)).mpr hratio
  rw [Real.log_div (ne_of_gt hyp) (ne_of_gt hy),
    Real.log_div (ne_of_gt hxp) (ne_of_gt hx)] at hlog
  exact hlog

noncomputable def sourceSaltLogF (delta : ℝ) (n : ℕ) : ℝ :=
  -(delta / (2 * Real.pi)) * Real.log (n : ℝ)

theorem sourceSaltLogF_diff (delta : ℝ) (n : ℕ) :
    sourceSaltLogF delta (n + 1) - sourceSaltLogF delta n =
      -(delta / (2 * Real.pi)) *
        (Real.log ((n:ℝ) + 1) - Real.log (n : ℝ)) := by
  unfold sourceSaltLogF
  push_cast
  ring
theorem sourceSaltLogF_forward_monotone (delta : ℝ)
    (hd : 0 ≤ delta) (n : ℕ) (hn : 1 ≤ n) :
    sourceSaltLogF delta (n + 1) - sourceSaltLogF delta n ≤
      sourceSaltLogF delta (n + 2) - sourceSaltLogF delta (n + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmon := source_log_increment_antitone
    (n : ℝ) ((n:ℝ)+1) hnR (by linarith)
  rw [sourceSaltLogF_diff, sourceSaltLogF_diff]
  have hdelta : 0 ≤ delta / (2 * Real.pi) := by positivity
  have hbound := mul_le_mul_of_nonpos_left hmon (by linarith : -(delta / (2 * Real.pi)) ≤ 0)
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hbound
end Green64Analytic.CorrelationMellin

end

/-! ## SourceLogDiscreteWindow -/

section

/-! Finite-difference, rather than derivative, Kusmin–Landau windows,
with the actual natural endpoints U..4U. -/
namespace Green64Analytic.CorrelationMellin

theorem sourceSaltLogF_forward_window (delta : ℝ) (U n : ℕ)
    (hd : 0 < delta) (hU : 1 ≤ U)
    (hdU : delta ≤ (U : ℝ))
    (hnU : U ≤ n) (hn4 : n ≤ 4 * U) :
    let eps : ℝ := delta / (40 * (U : ℝ))
    0 < eps ∧ eps ≤ 1/2 ∧
    (-1 : ℝ) + eps ≤
      sourceSaltLogF delta (n + 1) - sourceSaltLogF delta n ∧
    sourceSaltLogF delta (n + 1) - sourceSaltLogF delta n ≤ -eps := by
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hUpos (by exact_mod_cast hnU)
  have hnUreal : (U:ℝ) ≤ (n:ℝ) := by exact_mod_cast hnU
  have hn5nat : n + 1 ≤ 5 * U := by omega
  have hn5 : (n:ℝ) + 1 ≤ 5 * (U:ℝ) := by exact_mod_cast hn5nat
  have hdcoef : 0 < delta / (2 * Real.pi) := by positivity
  have hinc := source_log_increment_bounds (n:ℝ) hnpos
  let eps : ℝ := delta / (40 * (U:ℝ))
  have hepspos : 0 < eps := by dsimp [eps]; positivity
  have hepssmall : eps ≤ 1/40 := by
    dsimp [eps]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 40 * (U:ℝ))).mpr
    nlinarith [hdU]
  have hlowerden : 2 * Real.pi * ((n:ℝ) + 1) ≤ 40 * (U:ℝ) := by
    have hp : 2 * Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
    have hm : 2 * Real.pi * ((n:ℝ)+1) ≤ 8 * ((n:ℝ)+1) :=
      mul_le_mul_of_nonneg_right hp (by linarith [hnpos])
    nlinarith [hm, hn5]
  have hdenpos : 0 < 2 * Real.pi * ((n:ℝ)+1) := by positivity
  have hgainlower : eps ≤ (delta/(2*Real.pi)) *
      (((n:ℝ)+1)⁻¹) := by
    have hden1 : eps ≤ delta / (2 * Real.pi * ((n:ℝ)+1)) := by
      dsimp [eps]
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 40*(U:ℝ)) hdenpos]
      nlinarith [mul_nonneg (le_of_lt hd) (sub_nonneg.mpr hlowerden)]
    calc
      eps ≤ delta/(2*Real.pi*((n:ℝ)+1)) := hden1
      _ = delta/(2*Real.pi)*(((n:ℝ)+1)⁻¹) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
        ring
  have hgainhi : (delta/(2*Real.pi)) * ((n:ℝ)⁻¹) ≤ 1/6 := by
    have hpass : (n:ℝ)⁻¹ ≤ (U:ℝ)⁻¹ := inv_anti₀ hUpos hnUreal
    have hstar : (delta/(2*Real.pi)) * ((n:ℝ)⁻¹) ≤
        delta/(2*Real.pi)*(U:ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hpass (le_of_lt hdcoef)
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hlarge : 6 * delta ≤ 2 * Real.pi * (U:ℝ) := by
      have h6 : 6 * delta ≤ 6 * (U:ℝ) := by linarith [hdU]
      have hstrict : 6 * (U:ℝ) ≤ 2*Real.pi*(U:ℝ) := by
        nlinarith [mul_nonneg (le_of_lt hUpos) (le_of_lt (by linarith : 0 < 2*Real.pi-6))]
      exact h6.trans hstrict
    have hden : 0 < 2*Real.pi*(U:ℝ) := by positivity
    have hmid : delta/(2*Real.pi*(U:ℝ)) ≤ 1/6 := by
      rw [div_le_iff₀ hden]
      nlinarith [hlarge]
    have hrew : delta/(2*Real.pi)*(U:ℝ)⁻¹ =
        delta/(2*Real.pi*(U:ℝ)) := by ring
    exact hstar.trans (hrew ▸ hmid)
  have hgainlo : eps ≤ delta/(2*Real.pi) *
      (Real.log ((n:ℝ)+1)-Real.log (n:ℝ)) :=
    hgainlower.trans (mul_le_mul_of_nonneg_left hinc.1 (le_of_lt hdcoef))
  have hgainup : delta/(2*Real.pi) *
      (Real.log ((n:ℝ)+1)-Real.log (n:ℝ)) ≤ 1/6 :=
    (mul_le_mul_of_nonneg_left hinc.2 (le_of_lt hdcoef)).trans hgainhi
  have hdiff := sourceSaltLogF_diff delta n
  dsimp only
  refine ⟨hepspos, by linarith [hepssmall], ?_, ?_⟩
  · rw [hdiff]
    linarith [hepssmall, hgainup]
  · rw [hdiff]
    linarith [hgainlo]
end Green64Analytic.CorrelationMellin

end

/-! ## SourceLogFirstSum -/

section

/-! Unconditional first-derivative exponential sum on the actual
inclusive complete integer support [U,4U], U∈ℕ. -/
namespace Green64Analytic.CorrelationMellin

theorem sourceSaltLog_complete_first (delta : ℝ) (U : ℕ)
    (hd : 0 < delta) (hU : 1 ≤ U) (hdU : delta ≤ (U : ℝ)) :
    ‖∑ n ∈ Finset.Icc U (4 * U),
       Salt.ExpSum.eK (sourceSaltLogF delta n)‖
       ≤ 40 * (U : ℝ) / delta := by
  let eps : ℝ := delta / (40 * (U : ℝ))
  have hUi : U ≤ 4 * U := by omega
  have hWindowU := sourceSaltLogF_forward_window delta U U
    hd hU hdU le_rfl hUi
  have hepspos : 0 < eps := by
    simpa only [eps] using hWindowU.1
  have hepshalf : eps ≤ 1 / 2 := by
    simpa only [eps] using hWindowU.2.1
  have hLow (n : ℕ) (hn : U - 1 < n) (hnb : n ≤ 4 * U) :
      ((-1 : ℤ) : ℝ) + eps ≤ sourceSaltLogF delta (n + 1) -
        sourceSaltLogF delta n := by
    have hUn : U ≤ n := by omega
    have hw := sourceSaltLogF_forward_window delta U n hd hU hdU hUn hnb
    simpa only [eps, Int.cast_neg, Int.cast_one] using hw.2.2.1
  have hUp (n : ℕ) (hn : U - 1 < n) (hnb : n ≤ 4 * U) :
      sourceSaltLogF delta (n + 1) - sourceSaltLogF delta n ≤
      ((-1 : ℤ) : ℝ) + 1 - eps := by
    have hUn : U ≤ n := by omega
    have hw := sourceSaltLogF_forward_window delta U n hd hU hdU hUn hnb
    have hsimpl : ((-1 : ℤ) : ℝ) + 1 - eps = -eps := by norm_num
    rw [hsimpl]
    exact hw.2.2.2
  have hMono (n : ℕ) (hn : U - 1 < n) (_hn4 : n < 4 * U) :
      sourceSaltLogF delta (n + 1) - sourceSaltLogF delta n ≤
      sourceSaltLogF delta (n + 2) - sourceSaltLogF delta (n + 1) := by
    have hN : 1 ≤ n := by omega
    exact sourceSaltLogF_forward_monotone delta (le_of_lt hd) n hN
  have hKusmin :
      ‖∑ n ∈ Finset.Ioc (U - 1) (4 * U),
          Salt.ExpSum.eK (sourceSaltLogF delta n)‖ ≤ 1 / eps :=
    Salt.ExpSum.kusmin_landau (f := sourceSaltLogF delta)
      (a := U-1) (b := 4*U) (δ := eps) (m := -1)
      hepspos hepshalf hLow hUp hMono
  have heq : Finset.Ioc (U-1) (4*U) = Finset.Icc U (4*U) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hdne : delta ≠ 0 := ne_of_gt hd
  have hcalc : 1 / eps = 40 * (U:ℝ) / delta := by
    dsimp [eps]
    field_simp
  rw [← heq]
  calc
    _ ≤ 1 / eps := hKusmin
    _ = 40 * (U:ℝ) / delta := hcalc
end Green64Analytic.CorrelationMellin

end

/-! ## SourceLogSecondIncrement -/

section

/-! Exact analytic identity for the second forward difference of log.
This transfers continuous curvature to the natural integer grid without
unproved derivative tests or arithmetic endpoints. -/
namespace Green64Analytic.CorrelationMellin

theorem source_log_second_increment_identity (x : ℝ) (hx : 0 < x) :
    Real.log (x + 1) - Real.log x -
        (Real.log (x + 2) - Real.log (x + 1)) =
      Real.log (1 + (x * (x + 2))⁻¹) := by
  have hx1 : 0 < x + 1 := by linarith
  have hx2 : 0 < x + 2 := by linarith
  have hden : 0 < x * (x + 2) := mul_pos hx hx2
  have hfrac : ((x + 1)^2) / (x * (x + 2)) =
      1 + (x * (x + 2))⁻¹ := by
    field_simp
    ring
  rw [← hfrac, Real.log_div (pow_ne_zero _ (ne_of_gt hx1)) (ne_of_gt hden),
    Real.log_pow, Real.log_mul (ne_of_gt hx) (ne_of_gt hx2)]
  ring

theorem source_log_one_add_bounds (u : ℝ) (hu : 0 ≤ u) :
    u / (1 + u) ≤ Real.log (1 + u) ∧
    Real.log (1 + u) ≤ u := by
  have hpos : 0 < 1 + u := by linarith
  have hup : Real.log (1 + u) ≤ u := by
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlo := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hlo
  have heq : (1 + u)⁻¹ - 1 = -(u / (1 + u)) := by
    field_simp
    ring
  rw [heq] at hlo
  constructor <;> linarith
end Green64Analytic.CorrelationMellin

end

/-! ## SourceLogSecondWindow -/

section

/-! Unconditional finite second-difference curvature bounds for sampled log,
prior to the discrete van der Corput test. -/
namespace Green64Analytic.CorrelationMellin

theorem source_log_second_increment_bounds (x : ℝ) (hx : 1 ≤ x) :
    ((x * (x + 2))⁻¹) / 2 ≤
      Real.log (x + 1) - Real.log x -
        (Real.log (x + 2) - Real.log (x + 1)) ∧
    Real.log (x + 1) - Real.log x -
        (Real.log (x + 2) - Real.log (x + 1)) ≤
      (x * (x + 2))⁻¹ := by
  have hxpos : 0 < x := by linarith
  have hdenpos : 0 < x * (x + 2) := by positivity
  have hden : 1 ≤ x * (x + 2) := by nlinarith [hx]
  let u : ℝ := (x * (x + 2))⁻¹
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    simpa using (inv_anti₀ (by norm_num : (0:ℝ)<1) hden)
  have hp : 0 < 1 + u := by linarith
  have hlow : u / 2 ≤ u / (1 + u) := by
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ)<2) hp]
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hu1)]
  have hlog := source_log_one_add_bounds u hu
  have hiden := source_log_second_increment_identity x hxpos
  rw [hiden]
  exact ⟨hlow.trans hlog.1, hlog.2⟩

theorem sourceSaltLogF_second_diff (delta : ℝ) (n : ℕ) :
    (sourceSaltLogF delta (n + 2) -
      sourceSaltLogF delta (n + 1)) -
      (sourceSaltLogF delta (n + 1) -
        sourceSaltLogF delta n) =
    (delta / (2 * Real.pi)) *
      (Real.log ((n:ℝ)+1) - Real.log (n:ℝ) -
        (Real.log ((n:ℝ)+2) - Real.log ((n:ℝ)+1))) := by
  unfold sourceSaltLogF
  push_cast
  ring

theorem sourceSaltLogF_second_window (delta : ℝ) (U n : ℕ)
    (hd : 0 < delta) (hU : 1 ≤ U)
    (hnU : U ≤ n) (hn4 : n ≤ 4*U) :
    let lam : ℝ := (delta / (2 * Real.pi)) *
      (((6 * (U:ℝ))^2)⁻¹) / 2
    0 < lam ∧
    lam ≤ (sourceSaltLogF delta (n + 2) -
      sourceSaltLogF delta (n + 1)) -
      (sourceSaltLogF delta (n + 1) -
        sourceSaltLogF delta n) ∧
    (sourceSaltLogF delta (n + 2) -
      sourceSaltLogF delta (n + 1)) -
      (sourceSaltLogF delta (n + 1) -
        sourceSaltLogF delta n) ≤ 72 * lam := by
  have hUpos : (0:ℝ) < U := by exact_mod_cast hU
  have hnpos : (0:ℝ) < n :=
    lt_of_lt_of_le hUpos (by exact_mod_cast hnU)
  have hnUreal : (U:ℝ) ≤ n := by exact_mod_cast hnU
  have hn6nat : n + 2 ≤ 6 * U := by omega
  have hn6 : (n:ℝ)+2 ≤ 6*(U:ℝ) := by exact_mod_cast hn6nat
  have hn6lo : (n:ℝ) ≤ 6*(U:ℝ) := by linarith
  have hdenpos : 0 < (n:ℝ)*((n:ℝ)+2) := by positivity
  have hdenlo : (U:ℝ)^2 ≤ (n:ℝ)*((n:ℝ)+2) := by
    nlinarith [sq_nonneg ((n:ℝ)-(U:ℝ))]
  have hdenhi : (n:ℝ)*((n:ℝ)+2) ≤ (6*(U:ℝ))^2 := by
    calc
      _ ≤ (6*(U:ℝ))*((n:ℝ)+2) :=
        mul_le_mul_of_nonneg_right hn6lo (by positivity)
      _ ≤ (6*(U:ℝ))*(6*(U:ℝ)) :=
        mul_le_mul_of_nonneg_left hn6 (by positivity)
      _ = _ := by ring
  have hU2pos : (0:ℝ) < (U:ℝ)^2 := by positivity
  have hinvhi : ((6*(U:ℝ))^2)⁻¹ ≤
      ((n:ℝ)*((n:ℝ)+2))⁻¹ := inv_anti₀ hdenpos hdenhi
  have hinvlo : ((n:ℝ)*((n:ℝ)+2))⁻¹ ≤
      ((U:ℝ)^2)⁻¹ := inv_anti₀ hU2pos hdenlo
  have hn1 : (1:ℝ) ≤ n := by
    have hUn : (1:ℝ) ≤ U := by exact_mod_cast hU
    exact hUn.trans hnUreal
  have hcurv := source_log_second_increment_bounds (n:ℝ) hn1
  have hcoef : 0 ≤ delta/(2*Real.pi) := by positivity
  let lam : ℝ := (delta / (2 * Real.pi)) *
      (((6 * (U:ℝ))^2)⁻¹) / 2
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hlow : lam ≤ (delta/(2*Real.pi)) *
      (Real.log ((n:ℝ)+1)-Real.log (n:ℝ) -
        (Real.log ((n:ℝ)+2)-Real.log ((n:ℝ)+1))) := by
    calc
      lam ≤ (delta/(2*Real.pi))*(((n:ℝ)*((n:ℝ)+2))⁻¹)/2 := by
        dsimp [lam]
        gcongr
      _ = (delta/(2*Real.pi)) *
          (((n:ℝ)*((n:ℝ)+2))⁻¹ / 2) := by ring
      _ ≤ (delta/(2*Real.pi)) *
        (Real.log ((n:ℝ)+1)-Real.log (n:ℝ) -
          (Real.log ((n:ℝ)+2)-Real.log ((n:ℝ)+1))) :=
        mul_le_mul_of_nonneg_left hcurv.1 hcoef
  have hupper0 : (delta/(2*Real.pi)) *
      (Real.log ((n:ℝ)+1)-Real.log (n:ℝ) -
        (Real.log ((n:ℝ)+2)-Real.log ((n:ℝ)+1))) ≤
      (delta/(2*Real.pi))*(((U:ℝ)^2)⁻¹) := by
    calc
      _ ≤ (delta/(2*Real.pi))*(((n:ℝ)*((n:ℝ)+2))⁻¹) :=
        mul_le_mul_of_nonneg_left hcurv.2 hcoef
      _ ≤ _ := mul_le_mul_of_nonneg_left hinvlo hcoef
  have hrat : (delta/(2*Real.pi))*(((U:ℝ)^2)⁻¹) = 72*lam := by
    dsimp [lam]
    field_simp [ne_of_gt hUpos, Real.pi_ne_zero]
    ring
  have hexact := sourceSaltLogF_second_diff delta n
  have hboundlo :
      lam ≤ (sourceSaltLogF delta (n + 2) -
        sourceSaltLogF delta (n + 1)) -
        (sourceSaltLogF delta (n + 1) - sourceSaltLogF delta n) := by
    rw [hexact]
    exact hlow
  have hboundhi :
      (sourceSaltLogF delta (n + 2) -
        sourceSaltLogF delta (n + 1)) -
        (sourceSaltLogF delta (n + 1) - sourceSaltLogF delta n) ≤
      72*lam := by
    rw [hexact, ← hrat]
    exact hupper0
  exact ⟨hlam,hboundlo,hboundhi⟩
end Green64Analytic.CorrelationMellin

end

/-! ## SourceLogSecondRational -/

section

/-! A rational-constant second-difference window.  Replacing π by
3 < π < 4 makes the subsequent √λ normalization exact. -/
namespace Green64Analytic.CorrelationMellin

theorem sourceSaltLogF_second_rational (delta : ℝ) (U n : ℕ)
    (hd : 0 < delta) (hU : 1 ≤ U)
    (hnU : U ≤ n) (hn4 : n ≤ 4*U) :
    let lam : ℝ := delta / (576 * (U:ℝ)^2)
    0 < lam ∧
    lam ≤ (sourceSaltLogF delta (n + 2) -
      sourceSaltLogF delta (n + 1)) -
      (sourceSaltLogF delta (n + 1) -
        sourceSaltLogF delta n) ∧
    (sourceSaltLogF delta (n + 2) -
      sourceSaltLogF delta (n + 1)) -
      (sourceSaltLogF delta (n + 1) -
        sourceSaltLogF delta n) ≤ 96 * lam := by
  have hUpos : (0:ℝ) < U := by exact_mod_cast hU
  have hU2pos : (0:ℝ) < (U:ℝ)^2 := by positivity
  let lam : ℝ := delta / (576 * (U:ℝ)^2)
  let lamOld : ℝ := (delta/(2*Real.pi)) *
    (((6*(U:ℝ))^2)⁻¹)/2
  have hOld := sourceSaltLogF_second_window delta U n hd hU hnU hn4
  change 0 < lamOld ∧
    lamOld ≤ (sourceSaltLogF delta (n + 2) -
      sourceSaltLogF delta (n + 1)) -
      (sourceSaltLogF delta (n + 1) -
        sourceSaltLogF delta n) ∧
    (sourceSaltLogF delta (n + 2) -
      sourceSaltLogF delta (n + 1)) -
      (sourceSaltLogF delta (n + 1) -
        sourceSaltLogF delta n) ≤ 72 * lamOld at hOld
  have hOldEq : lamOld = delta/(144*Real.pi*(U:ℝ)^2) := by
    dsimp [lamOld]
    field_simp [ne_of_gt hUpos, Real.pi_ne_zero]
    ring
  have hNew : 0 < lam := by dsimp [lam]; positivity
  have hDenLo : 144*Real.pi*(U:ℝ)^2 ≤ 576*(U:ℝ)^2 := by
    have hpi : 144*Real.pi ≤ 576 := by linarith [Real.pi_lt_four]
    exact mul_le_mul_of_nonneg_right hpi (sq_nonneg _)
  have hLowerCompare : lam ≤ lamOld := by
    rw [hOldEq]
    dsimp [lam]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ)<576*(U:ℝ)^2)
      (by positivity : (0:ℝ)<144*Real.pi*(U:ℝ)^2)]
    exact mul_le_mul_of_nonneg_left hDenLo (le_of_lt hd)
  have hOldUpEq : 72 * lamOld = delta/(2*Real.pi*(U:ℝ)^2) := by
    rw [hOldEq]
    field_simp [ne_of_gt hUpos, Real.pi_ne_zero]
    ring
  have hNewUpEq : 96 * lam = delta/(6*(U:ℝ)^2) := by
    dsimp [lam]
    field_simp [ne_of_gt hUpos]
    ring
  have hDenHi : 6*(U:ℝ)^2 ≤ 2*Real.pi*(U:ℝ)^2 := by
    have hpi : 6 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
    exact mul_le_mul_of_nonneg_right hpi (sq_nonneg _)
  have hUpperCompare : 72 * lamOld ≤ 96 * lam := by
    rw [hOldUpEq, hNewUpEq]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ)<2*Real.pi*(U:ℝ)^2)
      (by positivity : (0:ℝ)<6*(U:ℝ)^2)]
    exact mul_le_mul_of_nonneg_left hDenHi (le_of_lt hd)
  exact ⟨hNew, hLowerCompare.trans hOld.2.1,
    hOld.2.2.trans hUpperCompare⟩
end Green64Analytic.CorrelationMellin

end

/-! ## SourceSaltVdCorput2 -/

section

/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# van der Corput's second-derivative test (Milestone 2)

This file discharges the `VK-N2-M2` residual: the discrete second-derivative
test built on top of `kusmin_landau` (Milestone 1, `Salt/ExpSum/Kusmin.lean`).

With `g n := f (n+1) - f n` the consecutive differences, if the second
differences satisfy `lam ≤ g (n+1) - g n ≤ c · lam` on the range (`0 < lam`,
`1 ≤ c`), then for `L := (b : ℝ) - a`,
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 8 · (c · L · √lam + 1 / √lam)`.

See the file `Kusmin.lean`'s Milestone-2 docstring for the full paper
arithmetic.  The engine here:

* `step_accum` — accumulate a per-step difference bound `g (n+1) - g n ≤ β`
  into `g q - g p ≤ (q - p) · β`.  Used twice (with `β = c·lam` and, via `-g`,
  with the lower bound `lam`).
* `fibre_is_interval` — **the sub-obstacle**: a `g`-monotone-predicate filter of
  an interval `Ioc a b` is itself a `Finset.Ioc`.  Built by hand from strict
  monotonicity via `min'`/`max'` (no mathlib shortcut exists for a general
  monotone predicate).  This is what lets each good window feed `kusmin_landau`.
* `count_window` — a window of `g`-length `w` holds `≤ w/lam + 1` indices, since
  `g` steps up by `≥ lam`.  Bounds the two bad windows per fibre.

**Constant.**  The recorded arithmetic advertised `C' = 5` using the (in general
false) step `⌊x⌋ - ⌊y⌋ ≤ x - y`; the honest fibre count is `K ≤ c·lam·L + 2`,
which lands the constant at `C' = 8` (explicitly permitted by the task).
-/

namespace Salt.ExpSum

open Real Finset

/-- **Step accumulation.**  If `g (n+1) - g n ≤ β` for every `n` strictly inside
`(a, b)`, then `g q - g p ≤ (q - p) · β` for `a < p ≤ q ≤ b`. -/
lemma step_accum {g : ℕ → ℝ} {a b : ℕ} {β : ℝ}
    (hstep : ∀ n, a < n → n < b → g (n + 1) - g n ≤ β)
    (p : ℕ) (hp : a < p) :
    ∀ q, p ≤ q → q ≤ b → g q - g p ≤ ((q : ℝ) - p) * β := by
  intro q hpq
  induction q, hpq using Nat.le_induction with
  | base => intro _; simp
  | succ q hpq ih =>
      intro hqb
      have h1 := ih (by omega)
      have h2 := hstep q (by omega) (by omega)
      have hexp : ((q + 1 : ℕ) : ℝ) - p = ((q : ℝ) - p) + 1 := by push_cast; ring
      rw [hexp, add_mul, one_mul]
      linarith

/-- **The fibre-is-an-interval lemma (the sub-obstacle).**  For a `g` strictly
monotone on `(a, b]` and reals `u ≤ v` (or any `u v`), the filter of `Ioc a b`
by the monotone predicate `u ≤ g n ∧ g n ≤ v` is a `Finset.Ioc a' b'` with
`a ≤ a'` and `b' ≤ b` (empty when `b' ≤ a'`). -/
lemma fibre_is_interval {g : ℕ → ℝ} {a b : ℕ}
    (hmono : ∀ p q, a < p → p < q → q ≤ b → g p < g q) (u v : ℝ) :
    ∃ a' b' : ℕ, a ≤ a' ∧ b' ≤ b ∧
      (Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n ≤ v) = Finset.Ioc a' b' := by
  set T := (Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n ≤ v) with hTdef
  rcases T.eq_empty_or_nonempty with he | hne
  · exact ⟨a, 0, le_refl a, Nat.zero_le b, by rw [he, Finset.Ioc_eq_empty (by omega)]⟩
  · have hn0mem : T.min' hne ∈ T := T.min'_mem hne
    have hn1mem : T.max' hne ∈ T := T.max'_mem hne
    set n0 := T.min' hne with hn0def
    set n1 := T.max' hne with hn1def
    obtain ⟨hn0Ioc, hn0lb, hn0ub⟩ := Finset.mem_filter.mp hn0mem
    obtain ⟨hn1Ioc, hn1lb, hn1ub⟩ := Finset.mem_filter.mp hn1mem
    obtain ⟨ha0, hb0⟩ := Finset.mem_Ioc.mp hn0Ioc
    obtain ⟨ha1, hb1⟩ := Finset.mem_Ioc.mp hn1Ioc
    refine ⟨n0 - 1, n1, by omega, hb1, ?_⟩
    ext x
    simp only [Finset.mem_Ioc]
    constructor
    · intro hx
      have hx0 : n0 ≤ x := Finset.min'_le T x hx
      have hx1 : x ≤ n1 := Finset.le_max' T x hx
      omega
    · rintro ⟨hlt, hle⟩
      have hx0 : n0 ≤ x := by omega
      have hxa : a < x := by omega
      have hxb : x ≤ b := le_trans hle hb1
      have hgx_lb : u ≤ g x := by
        rcases eq_or_lt_of_le hx0 with h | h
        · rw [← h]; exact hn0lb
        · exact le_trans hn0lb (le_of_lt (hmono n0 x ha0 h hxb))
      have hgx_ub : g x ≤ v := by
        rcases eq_or_lt_of_le hle with h | h
        · rw [h]; exact hn1ub
        · exact le_trans (le_of_lt (hmono x n1 hxa h hb1)) hn1ub
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hxa, hxb⟩, hgx_lb, hgx_ub⟩

/-- **Window count.**  If `g` steps up by `≥ lam > 0` (encoded via the lower
accumulation `hacc`), a window `[u, u+w)` of `g`-values holds at most
`w / lam + 1` indices in `Ioc a b`. -/
lemma count_window {g : ℕ → ℝ} {a b : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hacc : ∀ p q, a < p → p ≤ q → q ≤ b → ((q : ℝ) - p) * lam ≤ g q - g p)
    (u w : ℝ) (hw : 0 ≤ w) :
    (((Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n < u + w)).card : ℝ)
      ≤ w / lam + 1 := by
  set T := (Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n < u + w) with hTdef
  rcases T.eq_empty_or_nonempty with he | hne
  · rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    have : 0 ≤ w / lam := div_nonneg hw (le_of_lt hlam)
    linarith
  · have hn0mem : T.min' hne ∈ T := T.min'_mem hne
    have hn1mem : T.max' hne ∈ T := T.max'_mem hne
    set n0 := T.min' hne with hn0def
    set n1 := T.max' hne with hn1def
    obtain ⟨hn0Ioc, hn0lb, hn0ub⟩ := Finset.mem_filter.mp hn0mem
    obtain ⟨hn1Ioc, hn1lb, hn1ub⟩ := Finset.mem_filter.mp hn1mem
    obtain ⟨ha0, hb0⟩ := Finset.mem_Ioc.mp hn0Ioc
    obtain ⟨ha1, hb1⟩ := Finset.mem_Ioc.mp hn1Ioc
    have hn01 : n0 ≤ n1 := T.min'_le_max' hne
    have hsub : T ⊆ Finset.Icc n0 n1 := by
      intro x hx
      rw [Finset.mem_Icc]
      exact ⟨Finset.min'_le T x hx, Finset.le_max' T x hx⟩
    have hcard : T.card ≤ (Finset.Icc n0 n1).card := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hcardR : (T.card : ℝ) ≤ (n1 : ℝ) - n0 + 1 := by
      calc (T.card : ℝ) ≤ ((n1 + 1 - n0 : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = (n1 : ℝ) - n0 + 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hspread : ((n1 : ℝ) - n0) * lam ≤ g n1 - g n0 := hacc n0 n1 ha0 hn01 hb1
    have hgdiff : g n1 - g n0 < w := by linarith
    have hn1n0 : (n1 : ℝ) - n0 ≤ w / lam := by
      rw [le_div_iff₀ hlam]; linarith
    linarith

/-- **van der Corput's second-derivative test (Milestone 2).**

With `g n := f (n+1) - f n`, if the second differences satisfy
`lam ≤ g (n+1) - g n ≤ c · lam` for all `a < n < b` (`0 < lam`, `1 ≤ c`), then
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 8 · (c · (b - a) · √lam + 1 / √lam)`.

The absolute constant is `C' = 8` (the recorded arithmetic advertised `5` using
a step that is false in general; see the header). -/
theorem vdC_second_derivative {f : ℕ → ℝ} {a b : ℕ} {lam c : ℝ}
    (hab : a ≤ b) (hlam : 0 < lam) (hc : 1 ≤ c)
    (h2nd_lb : ∀ n, a < n → n < b →
        lam ≤ (f (n + 1 + 1) - f (n + 1)) - (f (n + 1) - f n))
    (h2nd_ub : ∀ n, a < n → n < b →
        (f (n + 1 + 1) - f (n + 1)) - (f (n + 1) - f n) ≤ c * lam) :
    ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
      ≤ 8 * (c * ((b : ℝ) - a) * Real.sqrt lam + 1 / Real.sqrt lam) := by
  set g : ℕ → ℝ := fun n => f (n + 1) - f n with hgdef
  set δ := Real.sqrt lam with hδdef
  have hδpos : 0 < δ := Real.sqrt_pos.mpr hlam
  have hne : δ ≠ 0 := ne_of_gt hδpos
  -- step bounds in terms of g
  have hstep_lb : ∀ n, a < n → n < b → lam ≤ g (n + 1) - g n := by
    intro n h1 h2; have := h2nd_lb n h1 h2; simpa only [hgdef] using this
  have hstep_ub : ∀ n, a < n → n < b → g (n + 1) - g n ≤ c * lam := by
    intro n h1 h2; have := h2nd_ub n h1 h2; simpa only [hgdef] using this
  -- accumulations
  have hacc_hi : ∀ p q, a < p → p ≤ q → q ≤ b → g q - g p ≤ ((q : ℝ) - p) * (c * lam) := by
    intro p q hp hpq hqb; exact step_accum hstep_ub p hp q hpq hqb
  have hacc_lo : ∀ p q, a < p → p ≤ q → q ≤ b → ((q : ℝ) - p) * lam ≤ g q - g p := by
    intro p q hp hpq hqb
    have hstep' : ∀ n, a < n → n < b → (fun m => -g m) (n + 1) - (fun m => -g m) n ≤ -lam := by
      intro n hn1 hn2; dsimp only; linarith [hstep_lb n hn1 hn2]
    have key : -g q - -g p ≤ ((q : ℝ) - p) * (-lam) :=
      step_accum (g := fun m => -g m) hstep' p hp q hpq hqb
    rw [mul_neg] at key; linarith
  have hstrictmono : ∀ p q, a < p → p < q → q ≤ b → g p < g q := by
    intro p q hp hpq hqb
    have h := hacc_lo p q hp (le_of_lt hpq) hqb
    have hpos : (0 : ℝ) < ((q : ℝ) - p) * lam := by
      apply mul_pos _ hlam
      have : (p : ℝ) < q := by exact_mod_cast hpq
      linarith
    linarith
  by_cases hsmall : lam ≤ 1 / 4
  · -- ═══ main case: lam ≤ 1/4 (δ ≤ 1/2) ═══
    have hδhalf : δ ≤ 1 / 2 := by
      rw [hδdef, show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hsmall
    have hδsq : lam = δ ^ 2 := by rw [hδdef]; exact (Real.sq_sqrt (le_of_lt hlam)).symm
    have hδlam : δ / lam = 1 / δ := by rw [hδsq, sq]; field_simp
    rcases eq_or_lt_of_le hab with hEq | haltb
    · -- empty: a = b
      have hEq2 : b = a := hEq.symm
      subst hEq2
      rw [Finset.Ioc_self, Finset.sum_empty, norm_zero]
      simp only [sub_self, mul_zero, zero_mul, zero_add]
      positivity
    · -- a < b
      have hLpos : (0 : ℝ) < (b : ℝ) - a := by
        have : (a : ℝ) < b := by exact_mod_cast haltb
        linarith
      have hLnn : (0 : ℝ) ≤ (b : ℝ) - a := le_of_lt hLpos
      set φ : ℕ → ℤ := fun n => ⌊g n⌋ with hφdef
      set K := (Finset.Ioc a b).image φ with hKdef
      have hmaps : ∀ n ∈ Finset.Ioc a b, φ n ∈ K := fun n hn => Finset.mem_image_of_mem φ hn
      -- STEP 1: triangle over fibres
      have hStep1 : ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
          ≤ ∑ k ∈ K, ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖ := by
        rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => eK (f n))]
        exact norm_sum_le _ _
      -- PER-FIBRE bound
      have hfibre : ∀ k ∈ K,
          ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖ ≤ 3 / δ + 2 := by
        intro k _
        set Fk := (Finset.Ioc a b).filter (fun n => φ n = k) with hFkdef
        set Gk := (Finset.Ioc a b).filter
          (fun n => (k : ℝ) + δ ≤ g n ∧ g n ≤ (k : ℝ) + 1 - δ) with hGkdef
        have hGsub : Gk ⊆ Fk := by
          intro n hn
          rw [hGkdef, Finset.mem_filter] at hn
          obtain ⟨hnIoc, hlb, hub⟩ := hn
          rw [hFkdef, Finset.mem_filter]
          refine ⟨hnIoc, ?_⟩
          rw [hφdef]
          exact Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
        have hsplit : ∑ n ∈ Fk, eK (f n)
            = (∑ n ∈ Fk \ Gk, eK (f n)) + (∑ n ∈ Gk, eK (f n)) :=
          (Finset.sum_sdiff hGsub).symm
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        -- good part via kusmin
        have hgood : ‖∑ n ∈ Gk, eK (f n)‖ ≤ 1 / δ := by
          obtain ⟨a', b', ha', hb', hGeq⟩ :=
            fibre_is_interval hstrictmono ((k : ℝ) + δ) ((k : ℝ) + 1 - δ)
          have hGkeq : Gk = Finset.Ioc a' b' := by rw [hGkdef]; exact hGeq
          rw [hGkeq]
          apply kusmin_landau hδpos hδhalf
          · intro n hn1 hn2
            have hnmem : n ∈ Gk := by rw [hGkeq]; exact Finset.mem_Ioc.mpr ⟨hn1, hn2⟩
            rw [hGkdef, Finset.mem_filter] at hnmem
            exact hnmem.2.1
          · intro n hn1 hn2
            have hnmem : n ∈ Gk := by rw [hGkeq]; exact Finset.mem_Ioc.mpr ⟨hn1, hn2⟩
            rw [hGkdef, Finset.mem_filter] at hnmem
            exact hnmem.2.2
          · intro n hn1 hn2
            exact le_of_lt (hstrictmono n (n + 1) (by omega) (by omega) (by omega))
        -- bad part via count_window
        have hbad : ‖∑ n ∈ Fk \ Gk, eK (f n)‖ ≤ 2 / δ + 2 := by
          have hcardbound : ((Fk \ Gk).card : ℝ) ≤ 2 / δ + 2 := by
            set Left := (Finset.Ioc a b).filter
              (fun n => (k : ℝ) ≤ g n ∧ g n < (k : ℝ) + δ) with hLeftdef
            set Right := (Finset.Ioc a b).filter
              (fun n => (k : ℝ) + 1 - δ ≤ g n ∧ g n < (k : ℝ) + 1 - δ + δ) with hRightdef
            have hsubLR : Fk \ Gk ⊆ Left ∪ Right := by
              intro n hn
              rw [Finset.mem_sdiff] at hn
              obtain ⟨hnFk, hnGk⟩ := hn
              rw [hFkdef, Finset.mem_filter] at hnFk
              obtain ⟨hnIoc, hφk⟩ := hnFk
              rw [hφdef] at hφk
              obtain ⟨hgk1, hgk2⟩ := Int.floor_eq_iff.mp hφk
              rw [hGkdef, Finset.mem_filter, not_and] at hnGk
              have hnotpred := hnGk hnIoc
              rw [not_and_or] at hnotpred
              rw [Finset.mem_union]
              rcases hnotpred with h | h
              · left
                rw [hLeftdef, Finset.mem_filter]
                rw [not_le] at h
                exact ⟨hnIoc, hgk1, h⟩
              · right
                rw [hRightdef, Finset.mem_filter]
                rw [not_le] at h
                refine ⟨hnIoc, le_of_lt h, ?_⟩
                have he : (k : ℝ) + 1 - δ + δ = (k : ℝ) + 1 := by ring
                rw [he]; exact hgk2
            have hcLR : (Fk \ Gk).card ≤ Left.card + Right.card :=
              le_trans (Finset.card_le_card hsubLR) (Finset.card_union_le Left Right)
            have hLeftC : (Left.card : ℝ) ≤ δ / lam + 1 :=
              count_window hlam hacc_lo (k : ℝ) δ (le_of_lt hδpos)
            have hRightC : (Right.card : ℝ) ≤ δ / lam + 1 :=
              count_window hlam hacc_lo ((k : ℝ) + 1 - δ) δ (le_of_lt hδpos)
            rw [hδlam] at hLeftC hRightC
            have hcast : ((Fk \ Gk).card : ℝ) ≤ (Left.card : ℝ) + (Right.card : ℝ) := by
              exact_mod_cast hcLR
            have hbridge : (2 : ℝ) / δ = 1 / δ + 1 / δ := by ring
            linarith [hcast, hLeftC, hRightC, hbridge]
          calc ‖∑ n ∈ Fk \ Gk, eK (f n)‖
              ≤ ∑ n ∈ Fk \ Gk, ‖eK (f n)‖ := norm_sum_le _ _
            _ = ∑ n ∈ Fk \ Gk, (1 : ℝ) := by simp [eK_norm]
            _ = ((Fk \ Gk).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            _ ≤ 2 / δ + 2 := hcardbound
        have hbridge : (3 : ℝ) / δ = 2 / δ + 1 / δ := by ring
        linarith [hgood, hbad, hbridge]
      -- STEP 2: sum the fibre bounds
      have hStep2 : ∑ k ∈ K,
          ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖
          ≤ (K.card : ℝ) * (3 / δ + 2) := by
        calc ∑ k ∈ K, ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖
            ≤ ∑ _k ∈ K, (3 / δ + 2) := Finset.sum_le_sum hfibre
          _ = (K.card : ℝ) * (3 / δ + 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      -- fibre count K ≤ c·lam·L + 2
      have hKcard : (K.card : ℝ) ≤ c * lam * ((b : ℝ) - a) + 2 := by
        have hφmono : ∀ n ∈ Finset.Ioc a b, φ (a + 1) ≤ φ n ∧ φ n ≤ φ b := by
          intro n hn
          obtain ⟨hna, hnb⟩ := Finset.mem_Ioc.mp hn
          simp only [hφdef]
          refine ⟨Int.floor_mono ?_, Int.floor_mono ?_⟩
          · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hna) with h | h
            · exact le_of_eq (congrArg g h)
            · exact le_of_lt (hstrictmono (a + 1) n (by omega) h hnb)
          · rcases eq_or_lt_of_le hnb with h | h
            · exact le_of_eq (congrArg g h)
            · exact le_of_lt (hstrictmono n b hna h (le_refl b))
        have hKsub : K ⊆ Finset.Icc (φ (a + 1)) (φ b) := by
          intro z hz
          rw [hKdef, Finset.mem_image] at hz
          obtain ⟨n, hn, rfl⟩ := hz
          rw [Finset.mem_Icc]
          exact hφmono n hn
        have hmemA : a + 1 ∈ Finset.Ioc a b :=
          Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
        have hφab : φ (a + 1) ≤ φ b := (hφmono (a + 1) hmemA).2
        have hcardZ : (K.card : ℤ) ≤ φ b + 1 - φ (a + 1) := by
          have h1 : K.card ≤ (Finset.Icc (φ (a + 1)) (φ b)).card := Finset.card_le_card hKsub
          have h2 : ((Finset.Icc (φ (a + 1)) (φ b)).card : ℤ) = φ b + 1 - φ (a + 1) := by
            rw [Int.card_Icc, Int.toNat_of_nonneg (show (0 : ℤ) ≤ φ b + 1 - φ (a + 1) by omega)]
          calc (K.card : ℤ) ≤ ((Finset.Icc (φ (a + 1)) (φ b)).card : ℤ) := by exact_mod_cast h1
            _ = φ b + 1 - φ (a + 1) := h2
        have hKR : (K.card : ℝ) ≤ (φ b : ℝ) + 1 - (φ (a + 1) : ℝ) := by
          calc (K.card : ℝ) = ((K.card : ℤ) : ℝ) := by push_cast; ring
            _ ≤ ((φ b + 1 - φ (a + 1) : ℤ) : ℝ) := by exact_mod_cast hcardZ
            _ = (φ b : ℝ) + 1 - (φ (a + 1) : ℝ) := by push_cast; ring
        have hfb : (φ b : ℝ) ≤ g b := by rw [hφdef]; exact Int.floor_le (g b)
        have hfa : g (a + 1) - 1 < (φ (a + 1) : ℝ) := by
          rw [hφdef]; exact Int.sub_one_lt_floor (g (a + 1))
        have hgub := hacc_hi (a + 1) b (by omega) (by omega) (le_refl b)
        have hclam : (0 : ℝ) ≤ c * lam := mul_nonneg (by linarith) (le_of_lt hlam)
        have hgub2 : g b - g (a + 1) ≤ c * lam * ((b : ℝ) - a) := by
          have hstep : ((b : ℝ) - (a + 1)) * (c * lam) ≤ c * lam * ((b : ℝ) - a) := by
            nlinarith [hclam]
          push_cast at hgub
          linarith [hgub, hstep]
        linarith [hKR, hfb, hfa, hgub2]
      -- FINAL arithmetic
      have hfinal : (K.card : ℝ) * (3 / δ + 2) ≤ 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := by
        have hcleared : (c * lam * ((b : ℝ) - a) + 2) * (3 + 2 * δ)
            ≤ 8 * (c * ((b : ℝ) - a) * δ) * δ + 8 := by
          rw [hδsq]
          nlinarith [hδpos, hδhalf, hLnn, hc,
            mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ c) hLnn) (sq_nonneg δ),
            mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ c) hLnn)
              (sq_nonneg δ)) (by linarith : (0 : ℝ) ≤ 5 - 2 * δ)]
        have e1 : (c * lam * ((b : ℝ) - a) + 2) * (3 / δ + 2)
            = ((c * lam * ((b : ℝ) - a) + 2) * (3 + 2 * δ)) / δ := by field_simp
        have e2 : 8 * (c * ((b : ℝ) - a) * δ + 1 / δ)
            = (8 * (c * ((b : ℝ) - a) * δ) * δ + 8) / δ := by field_simp
        calc (K.card : ℝ) * (3 / δ + 2)
            ≤ (c * lam * ((b : ℝ) - a) + 2) * (3 / δ + 2) :=
              mul_le_mul_of_nonneg_right hKcard (by positivity)
          _ = ((c * lam * ((b : ℝ) - a) + 2) * (3 + 2 * δ)) / δ := e1
          _ ≤ (8 * (c * ((b : ℝ) - a) * δ) * δ + 8) / δ :=
              (div_le_div_iff_of_pos_right hδpos).mpr hcleared
          _ = 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := e2.symm
      calc ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
          ≤ ∑ k ∈ K, ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖ := hStep1
        _ ≤ (K.card : ℝ) * (3 / δ + 2) := hStep2
        _ ≤ 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := hfinal
  · -- ═══ trivial case: lam > 1/4 (δ > 1/2) ═══
    have hbig : (1 : ℝ) / 4 < lam := not_le.mp hsmall
    have hδhalf : (1 : ℝ) / 2 < δ := by
      rw [hδdef, show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) hbig
    have hL : (0 : ℝ) ≤ (b : ℝ) - a := by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    have hnorm : ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖ ≤ (b : ℝ) - a := by
      calc ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
          ≤ ∑ n ∈ Finset.Ioc a b, ‖eK (f n)‖ := norm_sum_le _ _
        _ = ∑ n ∈ Finset.Ioc a b, (1 : ℝ) := by simp [eK_norm]
        _ = ((Finset.Ioc a b).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = (b : ℝ) - a := by rw [Nat.card_Ioc, Nat.cast_sub hab]
    have hcδ : (1 : ℝ) / 2 ≤ c * δ := by
      nlinarith [hc, hδhalf, hδpos, mul_nonneg (sub_nonneg.mpr hc) (le_of_lt hδpos)]
    have hbound : (b : ℝ) - a ≤ 8 * (c * ((b : ℝ) - a) * δ) := by
      nlinarith [hL, hcδ, mul_nonneg hL (by linarith [hcδ] : (0 : ℝ) ≤ c * δ - 1 / 2)]
    have h1δ : (0 : ℝ) ≤ 1 / δ := by positivity
    calc ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖ ≤ (b : ℝ) - a := hnorm
      _ ≤ 8 * (c * ((b : ℝ) - a) * δ) := hbound
      _ ≤ 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := by linarith

end Salt.ExpSum

end

/-! ## SourceLogSecondSum -/

section

/-! The van der Corput second-derivative estimate for the literal
natural interval [U,4U], without a postulated analytic sum inequality. -/
namespace Green64Analytic.CorrelationMellin

theorem sourceSaltLog_complete_second_raw (delta : ℝ) (U : ℕ)
    (hd : 0 < delta) (hU : 1 ≤ U) :
    ‖∑ n ∈ Finset.Icc U (4 * U),
       Salt.ExpSum.eK (sourceSaltLogF delta n)‖ ≤
      8 * (96 * (((4*U:ℕ):ℝ) - ((U-1:ℕ):ℝ)) *
          Real.sqrt (delta/(576*(U:ℝ)^2)) +
        1 / Real.sqrt (delta/(576*(U:ℝ)^2))) := by
  let lam : ℝ := delta / (576 * (U:ℝ)^2)
  have hUIoc : U-1 ≤ 4*U := by omega
  have hU4 : Finset.Ioc (U-1) (4*U) = Finset.Icc U (4*U) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hNew : 0 < lam := by dsimp [lam]; positivity
  have hLow (n : ℕ) (hn : U-1 < n) (hnb : n < 4*U) :
      lam ≤ (sourceSaltLogF delta (n+1+1) -
        sourceSaltLogF delta (n+1)) -
        (sourceSaltLogF delta (n+1) -
          sourceSaltLogF delta n) := by
    have hnU : U ≤ n := by omega
    have hWindow := sourceSaltLogF_second_rational delta U n
      hd hU hnU (by omega)
    simpa only [lam, Nat.add_assoc] using hWindow.2.1
  have hUp (n : ℕ) (hn : U-1 < n) (hnb : n < 4*U) :
      (sourceSaltLogF delta (n+1+1) -
        sourceSaltLogF delta (n+1)) -
        (sourceSaltLogF delta (n+1) -
          sourceSaltLogF delta n) ≤ 96*lam := by
    have hnU : U ≤ n := by omega
    have hWindow := sourceSaltLogF_second_rational delta U n
      hd hU hnU (by omega)
    simpa only [lam, Nat.add_assoc] using hWindow.2.2
  have hVdC := Salt.ExpSum.vdC_second_derivative
    (f := sourceSaltLogF delta) (a:=U-1) (b:=4*U)
    (lam:=lam) (c:=96) hUIoc hNew (by norm_num) hLow hUp
  rw [hU4] at hVdC
  simpa only [lam] using hVdC
end Green64Analytic.CorrelationMellin

end

/-! ## SourceLogSecondBound -/

section

/-! Explicit high-frequency estimate on the complete source block.
The parameter delta is a real frequency, not an integer. -/
namespace Green64Analytic.CorrelationMellin

theorem sourceSaltLog_complete_second (delta : ℝ) (U : ℕ)
    (hd : 0 < delta) (hU : 1 ≤ U) :
    ‖∑ n ∈ Finset.Icc U (4 * U),
        Salt.ExpSum.eK (sourceSaltLogF delta n)‖ ≤
      128 * Real.sqrt delta + 192 * (U:ℝ) / Real.sqrt delta := by
  have hUpos : (0:ℝ) < U := by exact_mod_cast hU
  have hsqrtPos : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hd
  have hlen : ((4*U:ℕ):ℝ) - ((U-1:ℕ):ℝ) ≤ 4*(U:ℝ) := by
    have hcast : ((4*U:ℕ):ℝ) = 4*(U:ℝ) := by push_cast; ring
    have hnonneg : (0:ℝ) ≤ (U-1:ℕ) := by positivity
    linarith
  have hsqrtEq : Real.sqrt (delta/(576*(U:ℝ)^2)) =
      Real.sqrt delta / (24*(U:ℝ)) := by
    have heq : 576*(U:ℝ)^2 = (24*(U:ℝ))^2 := by ring
    rw [heq, Real.sqrt_div (le_of_lt hd), Real.sqrt_sq_eq_abs,
      abs_of_pos (by positivity : 0<24*(U:ℝ))]
  have hInvEq : 1 / (Real.sqrt delta/(24*(U:ℝ))) =
      24*(U:ℝ)/Real.sqrt delta := by
    field_simp [ne_of_gt hsqrtPos, ne_of_gt hUpos]
  have hterm :
      96 * (((4*U:ℕ):ℝ) - ((U-1:ℕ):ℝ)) *
          (Real.sqrt delta/(24*(U:ℝ))) ≤ 16*Real.sqrt delta := by
    have hm : 96 * (((4*U:ℕ):ℝ) - ((U-1:ℕ):ℝ)) ≤
        96 * (4*(U:ℝ)) := by linarith [hlen]
    have hmul := mul_le_mul_of_nonneg_right hm
      (by positivity : 0 ≤ Real.sqrt delta/(24*(U:ℝ)))
    have hr : 96*(4*(U:ℝ))*(Real.sqrt delta/(24*(U:ℝ))) =
        16*Real.sqrt delta := by
      field_simp [ne_of_gt hUpos]
      ring
    linarith [hmul, hr]
  have hRaw := sourceSaltLog_complete_second_raw delta U hd hU
  rw [hsqrtEq, hInvEq] at hRaw
  calc
    _ ≤ 8 * (96 * (((4*U:ℕ):ℝ) - ((U-1:ℕ):ℝ)) *
        (Real.sqrt delta/(24*(U:ℝ))) +
        24*(U:ℝ)/Real.sqrt delta) := hRaw
    _ ≤ 8 * (16*Real.sqrt delta +
        24*(U:ℝ)/Real.sqrt delta) := by linarith [hterm]
    _ = _ := by ring
end Green64Analytic.CorrelationMellin

end

