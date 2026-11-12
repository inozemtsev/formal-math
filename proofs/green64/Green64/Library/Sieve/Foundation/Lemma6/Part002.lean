module

public import Green64.Library.ChenTheorem.Lemma6.StripGrowth
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Analysis.SumIntegralComparisons
public import Green64.Library.Sieve.Foundation.Analysis.Part001
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Green64.Library.Sieve.Foundation.LargeSieve.Part001
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Green64.Library.Sieve.Foundation.Lemma6.Part001
public import Green64.Library.PrimeNumberTheoremAnd.ZetaBounds

@[expose] public section

/-!
# Sieve / Foundation / Lemma6 / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ChenTheorem.Lemma6.LFunctionEulerBounds -/

section

open Set MeasureTheory
open scoped LSeries.notation ArithmeticFunction.Moebius

namespace Chen

theorem tsum_nat_rpow_neg_le (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, (n : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hsum := Real.summable_nat_rpow.mpr (show -σ < -1 by linarith)
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Ici ((1 : ℕ) : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -σ ≤ 0)).mono
      (fun t ht => by
        have ht' : (1 : ℝ) ≤ t := by simpa using ht
        change 0 < t
        linarith)
  have hint : IntegrableOn (fun t : ℝ => t ^ (-σ)) (Ioi ((1 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := fun t : ℝ => t ^ (-σ))
    (1 : ℕ) hanti hint (fun t ht => Real.rpow_nonneg (by
      have ht' : (1 : ℝ) < t := by simpa using ht
      linarith) _)
  have hi : (∫ t : ℝ in Ioi ((1 : ℕ) : ℝ), t ^ (-σ)) = 1 / (σ - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) (by norm_num)]
    norm_num only [Nat.cast_one, Real.one_rpow]
    field_simp [show σ - 1 ≠ 0 by linarith, show -σ + 1 ≠ 0 by linarith]
    ring
  rw [hi] at htail
  rw [← hsum.sum_add_tsum_nat_add 2]
  norm_num [Finset.sum_range_succ, Real.zero_rpow (by linarith : -σ ≠ 0)]
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num, one_div] using htail

theorem norm_LSeries_le_of_unit_bound (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : ‖LSeries f s‖ ≤ 1 + 1 / (s.re - 1) := by
  have hsum : LSeriesSummable f s := LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => hf n) hs
  have hpow := Real.summable_nat_rpow.mpr (show -s.re < -1 by linarith)
  calc
    ‖LSeries f s‖ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s.re) := by
      apply hsum.norm.tsum_le_tsum _ hpow
      intro n
      by_cases hn : n = 0
      · subst n
        simp [LSeries.term_zero, Real.zero_rpow (by linarith : -s.re ≠ 0)]
      · rw [LSeries.norm_term_eq, if_neg hn, Real.rpow_neg (Nat.cast_nonneg n)]
        exact (div_le_div_of_nonneg_right (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans_eq (one_div _)
    _ ≤ _ := tsum_nat_rpow_neg_le s.re hs

theorem norm_LFunction_euler_upper {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) : ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 1 / (s.re - 1) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact norm_LSeries_le_of_unit_bound _ (fun n => χ.norm_le_one n) s hs

/-- An absolute lower bound to the right of one, obtained from the
Möbius-twisted inverse series. It supplies an anchor for disk estimates. -/
theorem norm_LFunction_euler_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) : (s.re - 1) / s.re ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  have hmu : ∀ n : ℕ, ‖(↗χ * ↗μ) n‖ ≤ 1 := by
    intro n
    rw [Pi.mul_apply, norm_mul]
    have hm : ‖(μ n : ℂ)‖ ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    exact mul_le_one₀ (χ.norm_le_one n) (norm_nonneg _) hm
  have hb := norm_LSeries_le_of_unit_bound (↗χ * ↗μ) hmu s hs
  have hprod := congrArg norm (DirichletCharacter.LSeries.mul_mu_eq_one χ hs)
  rw [norm_mul, norm_one] at hprod
  have hB : 0 < 1 + 1 / (s.re - 1) := by positivity
  have hl : 1 / (1 + 1 / (s.re - 1)) ≤ ‖L ↗χ s‖ := by
    apply (div_le_iff₀ hB).mpr
    nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (L ↗χ s))]
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  convert hl using 1
  field_simp [show s.re - 1 ≠ 0 by linarith, show s.re ≠ 0 by linarith]
  ring

end Chen

end

/-! ## ChenTheorem.Lemma6.LFunctionDiskLogDerivative -/

section

open Set Metric

namespace Chen
/-- A primitive L-function has an explicit logarithmic-derivative estimate
in the three-quarter subdisk of a zero-free disk centered just to the right of one.
Only the zero-free disk remains an assumption: the growth and the lower
bound at its center are supplied by proved arithmetic estimates. -/
theorem norm_LFunction_logDeriv_le_of_nonvanishing_ball
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (c : ℂ) (R : ℝ)
    (hR : 0 < R) (hRsmall : R ≤ 1 / 4)
    (hc : 1 + R / 4 ≤ c.re) (hc2 : c.re ≤ 2)
    (hne : ∀ w ∈ ball c R, DirichletCharacter.LFunction χ w ≠ 0)
    (z : ℂ) (hz : dist z c ≤ 3 * R / 4) :
    ‖deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z‖ ≤
      224 * Real.log (48 * Real.sqrt q * Real.log (2 * q) * (‖c‖ + R) / R + 1) / R := by
  have hχne : χ ≠ 1 := by
    intro hχone
    have hcondOne : χ.conductor = 1 := DirichletCharacter.eq_one_iff_conductor_eq_one.mp hχone
    rw [DirichletCharacter.isPrimitive_def] at hχ
    omega
  let B : ℝ := 3 * Real.sqrt q * Real.log (2 * q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog : 0 < Real.log (2 * (q : ℝ)) := Real.log_pos (by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith)
  have hB : 0 < B := by dsimp [B]; positivity
  have hcre : 1 < c.re := by linarith
  have hanchor : R / 8 ≤ ‖DirichletCharacter.LFunction χ c‖ := by
    apply le_trans _ (norm_LFunction_euler_lower χ c hcre)
    apply (le_div_iff₀ (show 0 < c.re by linarith)).mpr
    nlinarith
  have hgrowth : ∀ w ∈ ball c R, ‖DirichletCharacter.LFunction χ w‖ ≤ 2 * B * (‖c‖ + R) := by
    intro w hw
    have hdist : ‖w - c‖ < R := by simpa only [mem_ball, dist_eq_norm] using hw
    have hrew : (1 / 2 : ℝ) ≤ w.re := by
      have hreal := Complex.abs_re_le_norm (w - c)
      rw [Complex.sub_re] at hreal
      have := (abs_le.mp hreal).1
      linarith
    have hn : ‖w‖ ≤ ‖c‖ + R := by
      have htriangle' : ‖w‖ ≤ ‖w - c‖ + ‖c‖ := norm_le_norm_sub_add w c
      linarith
    apply (norm_LFunction_le_of_re_pos hχ hq (by linarith : 0 < w.re)).trans
    change B * ‖w‖ / w.re ≤ _
    apply (div_le_iff₀ (show 0 < w.re by linarith)).mpr
    have hnormpos : 0 ≤ ‖c‖ + R := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hn hB.le,
      mul_le_mul_of_nonneg_left hrew (mul_nonneg hB.le hnormpos)]
  let A : ℝ := 16 * B * (‖c‖ + R) / R
  have hA : 0 < A := by dsimp [A]; positivity
  have hM : 0 < Real.log (A + 1) := Real.log_pos (by linarith)
  have hbound : ∀ w ∈ ball c R, ‖DirichletCharacter.LFunction χ w‖ ≤
      Real.exp (Real.log (A + 1)) * ‖DirichletCharacter.LFunction χ c‖ := by
    intro w hw
    rw [Real.exp_log (by linarith : 0 < A + 1)]
    apply (hgrowth w hw).trans
    have ha : 2 * B * (‖c‖ + R) ≤ A * ‖DirichletCharacter.LFunction χ c‖ := by
      dsimp [A]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hR).mpr
      nlinarith [mul_le_mul_of_nonneg_left hanchor (by positivity : 0 ≤ 16 * B * (‖c‖ + R))]
    nlinarith [norm_nonneg (DirichletCharacter.LFunction χ c)]
  have h := norm_logDeriv_le_of_nonvanishing_ball (DirichletCharacter.LFunction χ) c R
    (Real.log (A + 1)) hR hM (DirichletCharacter.differentiable_LFunction hχne).differentiableOn
    hne hbound z hz
  convert h using 1
  dsimp [A, B]
  congr 3
  ring
end Chen

end

/-! ## ChenTheorem.Lemma6.LFunctionLocalZeroLogDerivative -/

section

open Set Metric

namespace Chen

noncomputable def dirichletZeroDiskCenter (t : ℝ) : ℂ :=
  ((5 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I

noncomputable def dirichletZeroDiskBound (q : ℕ) (t : ℝ) : ℝ :=
  6 * Real.sqrt q * Real.log (2 * q) * (‖dirichletZeroDiskCenter t‖ + 1 / 2) + 1
theorem dirichletZeroDiskCenter_re (t : ℝ) : (dirichletZeroDiskCenter t).re = 5 / 4 := by
  simp [dirichletZeroDiskCenter]

theorem dirichletZeroDiskBound_ge_one (q : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    1 ≤ dirichletZeroDiskBound q t := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hl : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have : 0 ≤ 6 * Real.sqrt q * Real.log (2 * q) * (‖dirichletZeroDiskCenter t‖ + 1 / 2) := by positivity
  unfold dirichletZeroDiskBound
  linarith
theorem norm_LFunction_centered_disk_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive)
    (t : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + w)‖ ≤ dirichletZeroDiskBound q t := by
  let c := dirichletZeroDiskCenter t
  let B : ℝ := 3 * Real.sqrt q * Real.log (2 * q)
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hl : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hr : 1 / 2 ≤ (c + w).re := by
    have h := Complex.abs_re_le_norm w
    rw [Complex.add_re, dirichletZeroDiskCenter_re]
    have := (abs_le.mp h).1
    linarith
  have hn : ‖c + w‖ ≤ ‖c‖ + 1 / 2 := (norm_add_le c w).trans (by linarith)
  have h := norm_LFunction_le_of_re_pos hχ hq (show 0 < (c + w).re by linarith)
  change ‖DirichletCharacter.LFunction χ (c + w)‖ ≤ B * ‖c + w‖ / (c + w).re at h
  apply h.trans
  apply (div_le_iff₀ (by linarith : 0 < (c + w).re)).mpr
  have he : dirichletZeroDiskBound q t = 2 * B * (‖c‖ + 1 / 2) + 1 := by
    dsimp [dirichletZeroDiskBound, B, c]
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hn hB,
    mul_le_mul_of_nonneg_left hr (mul_nonneg hB (show 0 ≤ ‖c‖ + 1 / 2 by positivity))]
theorem norm_LFunction_zero_disk_center_ge {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 5 : ℝ) ≤ ‖DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t)‖ := by
  have h := norm_LFunction_euler_lower χ (dirichletZeroDiskCenter t)
    (by rw [dirichletZeroDiskCenter_re]; norm_num)
  norm_num only [dirichletZeroDiskCenter_re] at h
  exact h
/-- A primitive Dirichlet L-function admits a local zero-pole expansion
with an explicit growth error. The zeros may lie anywhere in the disk;
only the evaluation point is required to be nonzero. -/
theorem norm_LFunction_logDeriv_sub_local_zero_poles_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (t : ℝ)
    (s : ℂ) (hs : ‖s - dirichletZeroDiskCenter t‖ ≤ 9 / 32)
    (hne : DirichletCharacter.LFunction χ s ≠ 0) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
      diskZeroPoleSum (fun w => DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + w))
        (3 / 8) (s - dirichletZeroDiskCenter t)‖ ≤
      640 * (Real.log (5 * dirichletZeroDiskBound q t) + 1) := by
  let c := dirichletZeroDiskCenter t
  let F := fun w => DirichletCharacter.LFunction χ (c + w)
  let M := dirichletZeroDiskBound q t
  have hM : 1 ≤ M := dirichletZeroDiskBound_ge_one q hq t
  have hχne : χ ≠ 1 := by
    intro he
    have hcond := DirichletCharacter.eq_one_iff_conductor_eq_one.mp he
    rw [DirichletCharacter.isPrimitive_def] at hχ
    omega
  have hdiff : Differentiable ℂ F :=
    (DirichletCharacter.differentiable_LFunction hχne).comp (by fun_prop)
  have hf : AnalyticOnNhd ℂ F (closedBall 0 (4 * (3 / 8) / 3)) :=
    (hdiff.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  have hanchor : (1 / 5 : ℝ) ≤ ‖F 0‖ := by
    simpa only [F, add_zero] using norm_LFunction_zero_disk_center_ge χ t
  have hnorm0 : 0 < ‖F 0‖ := by linarith
  have hb : ∀ w ∈ sphere (0 : ℂ) (4 * (3 / 8) / 3), ‖F w‖ ≤ M := by
    intro w hw
    have hw' : ‖w‖ ≤ 1 / 2 := by norm_num [mem_sphere] at hw; exact hw.le
    exact norm_LFunction_centered_disk_le hq hχ t hw'
  have he : c + (s - c) = s := by ring
  have hmain := norm_logDeriv_sub_zero_poles_le_of_outer_bound (by norm_num : (0 : ℝ) < 3 / 8)
    hM hf (norm_pos_iff.mp hnorm0) hb
    (show ‖s - c‖ ≤ 3 * (3 / 8) / 4 by norm_num; exact hs)
    (show F (s - c) ≠ 0 by simpa only [F, he] using hne)
  have hd : deriv F (s - c) = deriv (DirichletCharacter.LFunction χ) s := by
    dsimp [F]
    rw [deriv_comp_const_add, he]
  rw [hd, show F (s - c) = DirichletCharacter.LFunction χ s by dsimp [F]; rw [he]] at hmain
  have hratio : M / ‖F 0‖ ≤ 5 * M := (div_le_iff₀ hnorm0).mpr (by nlinarith)
  have hlogs := Real.log_le_log (div_pos (by linarith : 0 < M) hnorm0) hratio
  apply hmain.trans
  change 240 * (Real.log (M / ‖F 0‖) + 1) / (3 / 8) ≤ 640 * (Real.log (5 * M) + 1)
  linarith
end Chen

end

/-! ## ChenTheorem.Lemma6.NonprincipalCompactGrowth -/

section

namespace Chen

theorem norm_dirichletEulerFactor_le_prime {d p : ℕ} (χ : DirichletCharacter ℂ d)
    (hp : p.Prime) {s : ℂ} (hs : 0 ≤ s.re) : ‖dirichletEulerFactor χ p s‖ ≤ (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hterm : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [norm_mul, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < p), Complex.neg_re]
    have hpow : (p : ℝ) ^ (-s.re) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ p)
        (by linarith : -s.re ≤ 0)
    exact mul_le_one₀ (χ.norm_le_one p) (Real.rpow_nonneg (Nat.cast_nonneg p) _) hpow
  have h := norm_sub_le (1 : ℂ) (χ p * (p : ℂ) ^ (-s))
  rw [norm_one] at h
  exact h.trans (by linarith)

theorem norm_dirichletEulerProduct_le_level {d q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ d) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∏ p ∈ q.primeFactors, dirichletEulerFactor χ p s‖ ≤ (q : ℝ) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ p ∈ q.primeFactors, (p : ℝ) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun p hp => norm_dirichletEulerFactor_le_prime χ
          (Nat.prime_of_mem_primeFactors hp) hs)
    _ ≤ q := by
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.prod_primeFactors_dvd q)

/-- A deliberately coarse uniform polynomial bound on the compact region
used by the Cauchy estimate in Siegel's argument. -/
theorem norm_nonprincipal_LFunction_compact_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ}
    (hs : (1 / 2 : ℝ) ≤ s.re) (hnorm : ‖s‖ ≤ 7 / 2) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 42 * (q : ℝ) ^ 3 := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hdne : χ.conductor ≠ 1 := fun h => hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
  have hd : 2 ≤ χ.conductor := by have := χ.conductor_ne_zero; omega
  have hdq : χ.conductor ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hdR : (2 : ℝ) ≤ χ.conductor := by exact_mod_cast hd
  have hdqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hdq
  have hqR : (2 : ℝ) ≤ q := hdR.trans hdqR
  have hprimitive : χ.primitiveCharacter ≠ 1 := by
    intro h
    have he := χ.changeLevel_primitiveCharacter
    rw [h, DirichletCharacter.changeLevel_one] at he
    exact hχ he.symm
  have he := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (s := s) (Or.inl hprimitive)
  rw [χ.changeLevel_primitiveCharacter] at he
  have hsqrt : Real.sqrt χ.conductor ≤ q := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg χ.conductor)
    have hmul := mul_nonneg (show 0 ≤ (χ.conductor : ℝ) - 1 by linarith)
      (Nat.cast_nonneg (α := ℝ) χ.conductor)
    nlinarith [Real.sqrt_nonneg χ.conductor]
  have hlog0 : 0 ≤ Real.log (2 * (χ.conductor : ℝ)) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2 * (χ.conductor : ℝ)) ≤ 2 * q :=
    (Real.log_le_self (by positivity)).trans (by linarith)
  have hbase : 3 * Real.sqrt χ.conductor * Real.log (2 * (χ.conductor : ℝ)) ≤ 6 * (q : ℝ) ^ 2 := by
    have hmul := mul_le_mul hsqrt hlog hlog0 (by linarith : (0 : ℝ) ≤ q)
    nlinarith
  have hratio : ‖s‖ / s.re ≤ (7 : ℝ) := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hp := norm_LFunction_le_of_re_pos χ.primitiveCharacter_isPrimitive hd (s := s) (by linarith)
  have hp' : ‖DirichletCharacter.LFunction χ.primitiveCharacter s‖ ≤ 42 * (q : ℝ) ^ 2 := by
    apply hp.trans
    calc
      _ = (3 * Real.sqrt χ.conductor * Real.log (2 * (χ.conductor : ℝ))) * (‖s‖ / s.re) := by ring
      _ ≤ (6 * (q : ℝ) ^ 2) * 7 :=
        mul_le_mul hbase hratio (div_nonneg (norm_nonneg _) (by linarith)) (by positivity)
      _ = _ := by ring
  rw [he, norm_mul]
  have heuler := norm_dirichletEulerProduct_le_level (q := q) χ.primitiveCharacter (s := s) (by linarith)
  calc
    _ ≤ (42 * (q : ℝ) ^ 2) * q := mul_le_mul hp' heuler (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Chen

end

/-! ## ChenTheorem.Lemma6.NonprincipalSmallPower -/

section

namespace Chen

/-- The L-function of every nonprincipal character has an arbitrarily small
conductor-power bound on a common neighborhood of one. -/
theorem exists_nonprincipal_small_power_disk {ε : ℝ} (hε : 0 < ε) :
    ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 2 ≤ q → χ ≠ 1 →
        ∀ s : ℂ, ‖s - 1‖ ≤ r → ‖DirichletCharacter.LFunction χ s‖ ≤ K * (q : ℝ) ^ ε := by
  obtain ⟨r, hr, hrsmall, hrR, hscale⟩ := exists_small_power_disk_radius hε
  let c : ℂ := ((1 + 2 * r : ℝ) : ℂ)
  have hcN : ‖c‖ = 1 + 2 * r := Complex.norm_of_nonneg (by linarith)
  have hAc : 1 ≤ 1 + 1 / r := by linarith [one_div_pos.mpr hr]
  refine ⟨r, (1 + 1 / r) * 42, hr, by positivity, ?_⟩
  intro q inst χ hq hχ s hs
  have hinner (w : ℂ) (hw : ‖w - c‖ ≤ r) : ‖DirichletCharacter.LFunction χ w‖ ≤ 1 + 1 / r := by
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (w - c)).trans hw)).1
    simp only [Complex.sub_re, c, Complex.ofReal_re] at hre
    have hwre : 1 < w.re := by linarith
    have hb := norm_LFunction_euler_upper χ w hwre
    have hi : 1 / (w.re - 1) ≤ 1 / r := one_div_le_one_div_of_le hr (by linarith)
    linarith
  have houter (w : ℂ) (hw : ‖w - c‖ ≤ (1 / 4 : ℝ)) :
      ‖DirichletCharacter.LFunction χ w‖ ≤ 42 * (q : ℝ) ^ 3 := by
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (w - c)).trans hw)).1
    simp only [Complex.sub_re, c, Complex.ofReal_re] at hre
    have hN := norm_add_le (w - c) c
    rw [sub_add_cancel, hcN] at hN
    apply norm_nonprincipal_LFunction_compact_le χ hχ (by linarith)
    linarith
  have hdist : ‖s - c‖ ≤ 3 * r := by
    have h := norm_add_le (s - 1) (1 - c)
    have hc : ‖(1 : ℂ) - c‖ = 2 * r := by
      change ‖(1 : ℂ) - ((1 + 2 * r : ℝ) : ℂ)‖ = 2 * r
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
      norm_num [show (1 : ℝ) - (1 + 2 * r) = -(2 * r) by ring, abs_of_pos hr]
    rw [sub_add_sub_cancel, hc] at h
    linarith
  exact norm_le_small_power_of_two_disks (DirichletCharacter.differentiable_LFunction hχ)
    hr hrR hAc (by norm_num) (by exact_mod_cast (by omega : 1 ≤ q)) hε.le hscale
    hinner houter hdist (hdist.trans hrsmall)

theorem exists_nonprincipal_LFunction_one_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ ≠ 1 → ‖DirichletCharacter.LFunction χ 1‖ ≤ K * (q : ℝ) ^ ε := by
  obtain ⟨r, K, hr, hK, h⟩ := exists_nonprincipal_small_power_disk hε
  refine ⟨K, hK, ?_⟩
  intro q inst χ hq hχ
  exact h q χ hq hχ 1 (by simpa using hr.le)

end Chen

end

/-! ## ChenTheorem.Lemma6.NonprincipalSmallPowerDerivative -/

section

namespace Chen

theorem exists_nonprincipal_deriv_small_power_disk {ε : ℝ} (hε : 0 < ε) :
    ∃ r D : ℝ, 0 < r ∧ 0 < D ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 2 ≤ q → χ ≠ 1 →
        ∀ s : ℂ, ‖s - 1‖ ≤ r →
          ‖deriv (DirichletCharacter.LFunction χ) s‖ ≤ D * (q : ℝ) ^ ε := by
  obtain ⟨r, K, hr, hK, h⟩ := exists_nonprincipal_small_power_disk hε
  refine ⟨r / 2, K / (r / 2), by positivity, by positivity, ?_⟩
  intro q inst χ hq hχ s hs
  have hbound (w : ℂ) (hw : w ∈ Metric.sphere s (r / 2)) :
      ‖DirichletCharacter.LFunction χ w‖ ≤ K * (q : ℝ) ^ ε := by
    have hwN : ‖w - s‖ = r / 2 := by simpa only [Metric.mem_sphere, dist_eq_norm] using hw
    have hN := norm_add_le (w - s) (s - 1)
    rw [sub_add_sub_cancel, hwN] at hN
    exact h q χ hq hχ w (by linarith)
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < r / 2)
    (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl hbound
  apply hd.trans_eq
  ring

/-- A zero near one bounds the value at one by its distance to one, with only
an arbitrarily small power of the conductor as loss. -/
theorem exists_nonprincipal_one_bound_of_real_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ r D : ℝ, 0 < r ∧ 0 < D ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 2 ≤ q → χ ≠ 1 →
        ∀ β : ℝ, 1 - r ≤ β → β ≤ 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
          ‖DirichletCharacter.LFunction χ 1‖ ≤ D * (q : ℝ) ^ ε * (1 - β) := by
  obtain ⟨r, D, hr, hD, hd⟩ := exists_nonprincipal_deriv_small_power_disk hε
  refine ⟨r, D, hr, hD, ?_⟩
  intro q inst χ hq hχ β hβ hβ' hz
  have hmem : (β : ℂ) ∈ Metric.closedBall (1 : ℂ) r := by
    rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : β - 1 ≤ 0)]
    linarith
  have hmem1 : (1 : ℂ) ∈ Metric.closedBall (1 : ℂ) r := Metric.mem_closedBall_self hr.le
  have h := (convex_closedBall (1 : ℂ) r).norm_image_sub_le_of_norm_deriv_le
    (fun s _ => (DirichletCharacter.differentiable_LFunction hχ) s)
    (fun s hs => hd q χ hq hχ s (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hs))
    hmem hmem1
  rw [hz, sub_zero, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_of_nonneg (sub_nonneg.mpr hβ')] at h
  exact h

end Chen

end

/-! ## ChenTheorem.Lemma6.ZeroFreeRegionData -/

section

open scoped Classical

namespace Chen

/-- The height-dependent width common to the classical nonexceptional
zero-free region and an ineffective Siegel bound with exponent `1 / N`. -/
noncomputable def primitiveZeroFreeWidthAt
    (N : ℕ) (cHeight cSiegel : ℝ) (q : ℕ) (t : ℝ) : ℝ :=
  min
    (cHeight / Real.log ((q : ℝ) * (|t| + 2)))
    (cSiegel * (q : ℝ) ^ ((-1 : ℝ) / N))
/-- The `N = 300` specialization used throughout the equation-(21)
development. -/
noncomputable def primitiveZeroFreeWidth
    (cHeight cSiegel : ℝ) (q : ℕ) (t : ℝ) : ℝ :=
  min
    (cHeight / Real.log ((q : ℝ) * (|t| + 2)))
    (cSiegel * (q : ℝ) ^ ((-1 : ℝ) / 300))

/-- The classical primitive-Dirichlet-`L` input needed for equation (21).
The nonvanishing assertion uses a strict boundary.  The companion
logarithmic-derivative estimate is required only in the half-width region;
this automatically lies strictly inside the nonvanishing region once the
width is positive.  Constants are absolute, while `cSiegel` is generally
ineffective. -/
structure PrimitiveZeroFreeRegionData where
  cHeight : ℝ
  cSiegel : ℝ
  cLogDeriv : ℝ
  cHeight_pos : 0 < cHeight
  cSiegel_pos : 0 < cSiegel
  cLogDeriv_pos : 0 < cLogDeriv
  nonvanishing :
    ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
        1 - primitiveZeroFreeWidth cHeight cSiegel q s.im < s.re →
          DirichletCharacter.LFunction χ s ≠ 0
  logDeriv_bound :
    ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
        1 - primitiveZeroFreeWidth cHeight cSiegel q s.im / 2 ≤ s.re →
          ‖deriv (DirichletCharacter.LFunction χ) s /
              DirichletCharacter.LFunction χ s‖ ≤
            cLogDeriv *
              ((q : ℝ) ^ ((1 : ℝ) / 300) +
                Real.log ((q : ℝ) * (|s.im| + 2)) + 1) ^ 2
/-- The same classical package with an arbitrary fixed positive Siegel
exponent denominator.  This family is needed for the arbitrary logarithmic
saving in the standalone Bombieri--Vinogradov theorem. -/
structure PrimitiveZeroFreeRegionDataAt (N : ℕ) where
  cHeight : ℝ
  cSiegel : ℝ
  cLogDeriv : ℝ
  cHeight_pos : 0 < cHeight
  cSiegel_pos : 0 < cSiegel
  cLogDeriv_pos : 0 < cLogDeriv
  nonvanishing :
    ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
        1 - primitiveZeroFreeWidthAt N cHeight cSiegel q s.im < s.re →
          DirichletCharacter.LFunction χ s ≠ 0
  logDeriv_bound :
    ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
        1 - primitiveZeroFreeWidthAt N cHeight cSiegel q s.im / 2 ≤ s.re →
          ‖deriv (DirichletCharacter.LFunction χ) s /
              DirichletCharacter.LFunction χ s‖ ≤
            cLogDeriv *
              ((q : ℝ) ^ ((1 : ℝ) / N) +
                Real.log ((q : ℝ) * (|s.im| + 2)) + 1) ^ 2
/-- Height-uniform logarithmic-derivative majorant for a finite rectangle,
at an arbitrary fixed Siegel exponent. -/
noncomputable def primitiveLogDerivMajorantAt
    {N : ℕ} (data : PrimitiveZeroFreeRegionDataAt N)
    (q : ℕ) (T : ℝ) : ℝ :=
  data.cLogDeriv *
    ((q : ℝ) ^ ((1 : ℝ) / N) +
      Real.log ((q : ℝ) * (T + 2)) + 1) ^ 2
theorem primitiveLogDerivMajorantAt_nonneg
    {N : ℕ} (data : PrimitiveZeroFreeRegionDataAt N)
    (q : ℕ) (T : ℝ) :
    0 ≤ primitiveLogDerivMajorantAt data q T := by
  unfold primitiveLogDerivMajorantAt
  exact mul_nonneg data.cLogDeriv_pos.le (sq_nonneg _)

/-- Existence of a classical mixed zero-free-region package. -/
def PrimitiveZeroFreeRegion : Prop :=
  Nonempty PrimitiveZeroFreeRegionData ∧
    ∀ N : ℕ, 1 ≤ N → Nonempty (PrimitiveZeroFreeRegionDataAt N)
theorem primitiveZeroFreeHeightLog_pos
    {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    0 < Real.log ((q : ℝ) * (|t| + 2)) := by
  apply Real.log_pos
  have hqcast : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have ht : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  nlinarith
theorem primitiveZeroFreeWidth_pos
    {cHeight cSiegel : ℝ} (hcHeight : 0 < cHeight)
    (hcSiegel : 0 < cSiegel) {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    0 < primitiveZeroFreeWidth cHeight cSiegel q t := by
  unfold primitiveZeroFreeWidth
  apply lt_min
  · exact div_pos hcHeight (primitiveZeroFreeHeightLog_pos hq t)
  · exact mul_pos hcSiegel (Real.rpow_pos_of_pos (by positivity) _)
/-- Positivity of the mixed width for an arbitrary fixed Siegel exponent. -/
theorem primitiveZeroFreeWidthAt_pos
    {N : ℕ} {cHeight cSiegel : ℝ} (hcHeight : 0 < cHeight)
    (hcSiegel : 0 < cSiegel) {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    0 < primitiveZeroFreeWidthAt N cHeight cSiegel q t := by
  unfold primitiveZeroFreeWidthAt
  apply lt_min
  · exact div_pos hcHeight (primitiveZeroFreeHeightLog_pos hq t)
  · exact mul_pos hcSiegel (Real.rpow_pos_of_pos (by positivity) _)

end Chen

end

/-! ## ChenTheorem.Lemma6.ZeroFreeWidthGeometry -/

section

open Set Metric

namespace Chen
/-- Moving the height by at most one quarter changes the conductor-height
logarithm by at most a factor of four thirds. -/
theorem conductor_height_log_le (q : ℕ) (hq : 2 ≤ q) (t u : ℝ)
    (htu : |u - t| ≤ 1 / 4) :
    Real.log ((q : ℝ) * (|u| + 2)) ≤ (4 / 3) * Real.log ((q : ℝ) * (|t| + 2)) := by
  let A : ℝ := (q : ℝ) * (|t| + 2)
  let B : ℝ := (q : ℝ) * (|u| + 2)
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hA : 4 ≤ A := by dsimp [A]; nlinarith [abs_nonneg t]
  have hB : 0 < B := by dsimp [B]; positivity
  have hAB : B ≤ (9 / 8) * A := by
    have hu : |u| ≤ |t| + 1 / 4 := by
      have := abs_sub_abs_le_abs_sub u t
      linarith
    dsimp [A, B]
    nlinarith [mul_le_mul_of_nonneg_left hu (show (0 : ℝ) ≤ q by positivity),
      mul_nonneg (show (0 : ℝ) ≤ q by positivity) (abs_nonneg t)]
  have hratio : B / A ≤ 9 / 8 := (div_le_iff₀ (by linarith : 0 < A)).mpr hAB
  have hlogratio := Real.log_le_sub_one_of_pos (div_pos hB (by linarith : 0 < A))
  rw [Real.log_div hB.ne' (show A ≠ 0 by linarith)] at hlogratio
  have hlogA := Real.one_sub_inv_le_log_of_pos (show 0 < A by linarith)
  have hinv : A⁻¹ ≤ (1 / 4 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hA
  change Real.log B ≤ (4 / 3) * Real.log A
  linarith
/-- The mixed zero-free width retains at least three quarters of its value
through a vertical displacement of size at most one quarter. -/
theorem primitiveZeroFreeWidthAt_height_comparison (N : ℕ) (cH cS : ℝ)
    (hcH : 0 ≤ cH) (hcS : 0 ≤ cS) (q : ℕ) (hq : 2 ≤ q) (t u : ℝ)
    (htu : |u - t| ≤ 1 / 4) :
    (3 / 4) * primitiveZeroFreeWidthAt N cH cS q t ≤ primitiveZeroFreeWidthAt N cH cS q u := by
  have hLt := primitiveZeroFreeHeightLog_pos hq t
  have hLu := primitiveZeroFreeHeightLog_pos hq u
  have hlogs := conductor_height_log_le q hq t u htu
  have hfirst : (3 / 4) * (cH / Real.log ((q : ℝ) * (|t| + 2))) ≤
      cH / Real.log ((q : ℝ) * (|u| + 2)) := by
    apply (le_div_iff₀ hLu).mpr
    calc
      _ = ((3 / 4) * cH * Real.log ((q : ℝ) * (|u| + 2))) /
          Real.log ((q : ℝ) * (|t| + 2)) := by ring
      _ ≤ cH := (div_le_iff₀ hLt).mpr (by
        nlinarith [mul_le_mul_of_nonneg_left hlogs hcH])
  have hsecond : (3 / 4) * (cS * (q : ℝ) ^ ((-1 : ℝ) / N)) ≤
      cS * (q : ℝ) ^ ((-1 : ℝ) / N) := by
    nlinarith [mul_nonneg hcS (Real.rpow_nonneg (Nat.cast_nonneg q) ((-1 : ℝ) / N))]
  unfold primitiveZeroFreeWidthAt
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  exact min_le_min hfirst hsecond
end Chen

end

/-! ## ChenTheorem.Lemma6.ZeroFreeRegionDisks -/

section

open Set Metric

namespace Chen

noncomputable def zeroFreeDiskCenter (R t : ℝ) : ℂ :=
  ((1 + R / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I

theorem zeroFreeDiskCenter_re (R t : ℝ) : (zeroFreeDiskCenter R t).re = 1 + R / 4 := by
  simp [zeroFreeDiskCenter]

theorem zeroFreeDiskCenter_im (R t : ℝ) : (zeroFreeDiskCenter R t).im = t := by
  simp [zeroFreeDiskCenter]
/-- The disk whose radius is the mixed width stays inside the full region,
even though the width varies with the imaginary coordinate. -/
theorem zeroFreeDisk_subset_region (N : ℕ) (cH cS : ℝ) (hcH : 0 < cH) (hcS : 0 < cS)
    (q : ℕ) (hq : 2 ≤ q) (t : ℝ)
    (hsmall : primitiveZeroFreeWidthAt N cH cS q t ≤ 1 / 4) :
    ∀ w ∈ ball (zeroFreeDiskCenter (primitiveZeroFreeWidthAt N cH cS q t) t)
      (primitiveZeroFreeWidthAt N cH cS q t),
      1 - primitiveZeroFreeWidthAt N cH cS q w.im < w.re := by
  intro w hw
  let R := primitiveZeroFreeWidthAt N cH cS q t
  have hn : ‖w - zeroFreeDiskCenter R t‖ < R := by
    simpa only [mem_ball, dist_eq_norm] using hw
  have hi := Complex.abs_im_le_norm (w - zeroFreeDiskCenter R t)
  rw [Complex.sub_im, zeroFreeDiskCenter_im] at hi
  have hheight : |w.im - t| ≤ 1 / 4 := by change R ≤ 1 / 4 at hsmall; linarith
  have hwidth := primitiveZeroFreeWidthAt_height_comparison N cH cS hcH.le hcS.le q hq t w.im hheight
  have hr := Complex.abs_re_le_norm (w - zeroFreeDiskCenter R t)
  rw [Complex.sub_re, zeroFreeDiskCenter_re] at hr
  have hre := (abs_le.mp hr).1
  change (3 / 4) * R ≤ _ at hwidth
  linarith
theorem half_width_point_mem_threeQuarterDisk (R : ℝ) (s : ℂ)
    (hlo : 1 - R / 2 ≤ s.re) (hhi : s.re ≤ 1 + R) :
    dist s (zeroFreeDiskCenter R s.im) ≤ 3 * R / 4 := by
  have heq : s - zeroFreeDiskCenter R s.im = ((s.re - (1 + R / 4) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [zeroFreeDiskCenter]
  rw [dist_eq_norm, heq, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
/-- Conditional only on nonvanishing in the full mixed region, the disk
estimate applies to every point of the half-width region near the line one.
No logarithmic-derivative estimate is assumed. -/
theorem norm_LFunction_logDeriv_le_of_mixed_region
    (N : ℕ) (cH cS : ℝ) (hcH : 0 < cH) (hcS : 0 < cS)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 2 ≤ q) (hχ : χ.IsPrimitive)
    (hne : ∀ w : ℂ, 1 - primitiveZeroFreeWidthAt N cH cS q w.im < w.re →
      DirichletCharacter.LFunction χ w ≠ 0)
    (s : ℂ) (hsmall : primitiveZeroFreeWidthAt N cH cS q s.im ≤ 1 / 4)
    (hlo : 1 - primitiveZeroFreeWidthAt N cH cS q s.im / 2 ≤ s.re)
    (hhi : s.re ≤ 1 + primitiveZeroFreeWidthAt N cH cS q s.im) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
      224 * Real.log (48 * Real.sqrt q * Real.log (2 * q) *
        (‖zeroFreeDiskCenter (primitiveZeroFreeWidthAt N cH cS q s.im) s.im‖ +
          primitiveZeroFreeWidthAt N cH cS q s.im) /
            primitiveZeroFreeWidthAt N cH cS q s.im + 1) /
              primitiveZeroFreeWidthAt N cH cS q s.im := by
  have hR := primitiveZeroFreeWidthAt_pos (N := N) hcH hcS hq s.im
  apply norm_LFunction_logDeriv_le_of_nonvanishing_ball hχ hq _ _ hR hsmall
  · rw [zeroFreeDiskCenter_re]
  · rw [zeroFreeDiskCenter_re]
    linarith
  · intro w hw
    exact hne w (zeroFreeDisk_subset_region N cH cS hcH hcS q hq s.im hsmall w hw)
  · exact half_width_point_mem_threeQuarterDisk _ s hlo hhi
end Chen

end

/-! ## ChenTheorem.Lemma6.ZeroFreeWidthScale -/

section

namespace Chen

noncomputable def primitiveZeroFreeScaleAt (N q : ℕ) (t : ℝ) : ℝ :=
  (q : ℝ) ^ ((1 : ℝ) / N) + Real.log ((q : ℝ) * (|t| + 2)) + 1
theorem conductor_height_log_ge_threeQuarters (q : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    (3 / 4 : ℝ) ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hA : 4 ≤ (q : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  have hlog := Real.one_sub_inv_le_log_of_pos (show 0 < (q : ℝ) * (|t| + 2) by linarith)
  have hinv : ((q : ℝ) * (|t| + 2))⁻¹ ≤ (1 / 4 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hA
  linarith
theorem primitiveZeroFreeWidthAt_le_quarter (N : ℕ) (cH cS : ℝ)
    (hcH : cH ≤ 1 / 8) (q : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    primitiveZeroFreeWidthAt N cH cS q t ≤ 1 / 4 := by
  apply (min_le_left _ _).trans
  apply (div_le_iff₀ (primitiveZeroFreeHeightLog_pos hq t)).mpr
  linarith [conductor_height_log_ge_threeQuarters q hq t]
/-- The reciprocal mixed width is controlled by the exact scale appearing
in the requested global logarithmic-derivative bound. -/
theorem inv_primitiveZeroFreeWidthAt_le_scale (N : ℕ) (cH cS : ℝ)
    (hcH : 0 < cH) (hcS : 0 < cS) (q : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    1 / primitiveZeroFreeWidthAt N cH cS q t ≤
      (1 / cH + 1 / cS) * primitiveZeroFreeScaleAt N q t := by
  have hL := primitiveZeroFreeHeightLog_pos hq t
  have hQ := Real.rpow_pos_of_pos (show (0 : ℝ) < q by exact_mod_cast (show 0 < q by omega)) ((1 : ℝ) / N)
  have hSL : Real.log ((q : ℝ) * (|t| + 2)) ≤ primitiveZeroFreeScaleAt N q t := by
    unfold primitiveZeroFreeScaleAt
    linarith
  have hSQ : (q : ℝ) ^ ((1 : ℝ) / N) ≤ primitiveZeroFreeScaleAt N q t := by
    unfold primitiveZeroFreeScaleAt
    linarith
  by_cases hm : cH / Real.log ((q : ℝ) * (|t| + 2)) ≤ cS * (q : ℝ) ^ ((-1 : ℝ) / N)
  · rw [primitiveZeroFreeWidthAt, min_eq_left hm, one_div_div]
    calc
      _ = (1 / cH) * Real.log ((q : ℝ) * (|t| + 2)) := by ring
      _ ≤ _ := mul_le_mul (by linarith [one_div_pos.mpr hcS]) hSL hL.le (by positivity)
  · rw [primitiveZeroFreeWidthAt, min_eq_right (le_of_not_ge hm)]
    have he : 1 / (cS * (q : ℝ) ^ ((-1 : ℝ) / N)) = (1 / cS) * (q : ℝ) ^ ((1 : ℝ) / N) := by
      rw [show (-1 : ℝ) / N = -((1 : ℝ) / N) by ring,
        Real.rpow_neg (Nat.cast_nonneg q)]
      field_simp
    rw [he]
    exact mul_le_mul (by linarith [one_div_pos.mpr hcH]) hSQ hQ.le (by positivity)
theorem zeroFreeDiskCenter_norm_add_radius_le (R t : ℝ) (hR : 0 < R) (hRsmall : R ≤ 1 / 4) :
    ‖zeroFreeDiskCenter R t‖ + R ≤ |t| + 3 := by
  have hc : ‖zeroFreeDiskCenter R t‖ ≤ 1 + R / 4 + |t| := by
    unfold zeroFreeDiskCenter
    calc
      _ ≤ ‖((1 + R / 4 : ℝ) : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
        mul_one, abs_of_pos (show 0 < 1 + R / 4 by linarith)]
  linarith

end Chen

end

/-! ## ChenTheorem.Lemma6.LFunctionLocalZeroScale -/

section

namespace Chen
theorem dirichletZeroDisk_log_bound_le (q : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    Real.log (5 * dirichletZeroDiskBound q t) + 1 ≤
      91 * Real.log ((q : ℝ) * (|t| + 2)) := by
  let A : ℝ := (q : ℝ) * (|t| + 2)
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hA : 4 ≤ A := by dsimp [A]; nlinarith [abs_nonneg t]
  have hqA : (q : ℝ) ≤ A := by dsimp [A]; nlinarith [abs_nonneg t]
  have hc : ‖dirichletZeroDiskCenter t‖ + 1 / 2 ≤ A := by
    have hn : ‖dirichletZeroDiskCenter t‖ ≤ 5 / 4 + |t| := by
      unfold dirichletZeroDiskCenter
      apply (norm_add_le _ _).trans_eq
      norm_num [norm_mul]
    dsimp [A]
    nlinarith [abs_nonneg t]
  have hsqrt : Real.sqrt (q : ℝ) ≤ A := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg q)
    have hn := Real.sqrt_nonneg (q : ℝ)
    nlinarith
  have hl : Real.log (2 * (q : ℝ)) ≤ 2 * A := by
    have h := Real.log_le_self (by positivity : (0 : ℝ) ≤ 2 * q)
    linarith
  have hlpos : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have hnum : 6 * Real.sqrt q * Real.log (2 * q) * (‖dirichletZeroDiskCenter t‖ + 1 / 2) ≤
      12 * A ^ 3 := by
    calc
      _ ≤ 6 * A * (2 * A) * A := by gcongr
      _ = _ := by ring
  have hApow : 1 ≤ A ^ 3 := one_le_pow₀ (by linarith : 1 ≤ A)
  have hM : dirichletZeroDiskBound q t ≤ 13 * A ^ 3 := by
    unfold dirichletZeroDiskBound
    linarith
  have hMpos := dirichletZeroDiskBound_ge_one q hq t
  have hlog := Real.log_le_log (by linarith : 0 < 5 * dirichletZeroDiskBound q t)
    (show 5 * dirichletZeroDiskBound q t ≤ 65 * A ^ 3 by linarith)
  rw [Real.log_mul (by norm_num : (65 : ℝ) ≠ 0) (by positivity : A ^ 3 ≠ 0),
    Real.log_pow] at hlog
  have h65 : Real.log 65 ≤ (65 : ℝ) := Real.log_le_self (by norm_num)
  have hL : (3 / 4 : ℝ) ≤ Real.log A := conductor_height_log_ge_threeQuarters q hq t
  change _ ≤ 91 * Real.log A
  norm_num only [Nat.cast_ofNat] at hlog
  linarith
/-- The local zero-pole expansion has an absolute conductor-height error,
uniform in every primitive character, without assuming a zero-free region. -/
theorem norm_LFunction_logDeriv_sub_local_zero_poles_le_log {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (t : ℝ)
    (s : ℂ) (hs : ‖s - dirichletZeroDiskCenter t‖ ≤ 9 / 32)
    (hne : DirichletCharacter.LFunction χ s ≠ 0) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
      diskZeroPoleSum (fun w => DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + w))
        (3 / 8) (s - dirichletZeroDiskCenter t)‖ ≤
      60000 * Real.log ((q : ℝ) * (|t| + 2)) := by
  apply (norm_LFunction_logDeriv_sub_local_zero_poles_le hq hχ t s hs hne).trans
  have h := dirichletZeroDisk_log_bound_le q hq t
  have hL := primitiveZeroFreeHeightLog_pos hq t
  linarith
end Chen

end

/-! ## ChenTheorem.Lemma6.LFunctionZeroPoleRealPart -/

section

open Set Metric

namespace Chen

theorem line_point_sub_dirichletZeroDiskCenter (σ t : ℝ) :
    (σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t = ((σ - 5 / 4 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [dirichletZeroDiskCenter]
theorem norm_line_point_sub_dirichletZeroDiskCenter_le {σ : ℝ}
    (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) (t : ℝ) :
    ‖(σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t‖ ≤ 9 / 32 := by
  rw [line_point_sub_dirichletZeroDiskCenter, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith
theorem primitive_centered_LFunction_analytic {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (t : ℝ) :
    AnalyticOnNhd ℂ (fun w => DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + w))
      (closedBall 0 (3 / 8)) := by
  have hχne : χ ≠ 1 := by
    intro he
    have hcond := DirichletCharacter.eq_one_iff_conductor_eq_one.mp he
    rw [DirichletCharacter.isPrimitive_def] at hχ
    omega
  have hd := (DirichletCharacter.differentiable_LFunction hχne).comp
    (show Differentiable ℂ (fun w => dirichletZeroDiskCenter t + w) by fun_prop)
  exact (hd.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
theorem centered_LFunction_ne_zero_of_re_gt_neg_quarter {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (w : ℂ) (hw : -(1 / 4 : ℝ) < w.re) :
    DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + w) ≠ 0 := by
  have hr : 1 < (dirichletZeroDiskCenter t + w).re := by
    rw [Complex.add_re, dirichletZeroDiskCenter_re]
    linarith
  apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr _) hr.le
  intro he
  rw [he] at hr
  norm_num at hr
theorem primitive_LFunction_local_zero_poles_re_nonneg {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ (diskZeroPoleSum
      (fun w => DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + w)) (3 / 8)
      ((σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t)).re := by
  apply diskZeroPoleSum_re_nonneg (κ := -(1 / 4 : ℝ)) (primitive_centered_LFunction_analytic hq hχ t)
    (fun w _ hw => centered_LFunction_ne_zero_of_re_gt_neg_quarter χ t w hw)
  rw [line_point_sub_dirichletZeroDiskCenter, Complex.ofReal_re]
  linarith
theorem primitive_LFunction_logDeriv_re_ge {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (σ t : ℝ)
    (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) :
    -(60000 * Real.log ((q : ℝ) * (|t| + 2))) ≤
      (deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
  have he : dirichletZeroDiskCenter t +
      ((σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t) =
      (σ : ℂ) + (t : ℂ) * Complex.I := by ring
  have hne := centered_LFunction_ne_zero_of_re_gt_neg_quarter χ t
    ((σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t)
    (by rw [line_point_sub_dirichletZeroDiskCenter, Complex.ofReal_re]; linarith)
  rw [he] at hne
  have hb := norm_LFunction_logDeriv_sub_local_zero_poles_le_log hq hχ t _
    (norm_line_point_sub_dirichletZeroDiskCenter_le hσ hσ' t) hne
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  rw [Complex.sub_re] at hr
  have hp := primitive_LFunction_local_zero_poles_re_nonneg hq hχ σ t hσ
  linarith
theorem primitive_LFunction_local_zero_poles_re_ge_single {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (σ β t : ℝ)
    (hσ : 1 < σ) (hβ : 7 / 8 < β)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + (t : ℂ) * Complex.I) = 0) :
    1 / (σ - β) ≤ (diskZeroPoleSum
      (fun w => DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + w)) (3 / 8)
      ((σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t)).re := by
  let c := dirichletZeroDiskCenter t
  let w := (β : ℂ) + (t : ℂ) * Complex.I - c
  let z := (σ : ℂ) + (t : ℂ) * Complex.I - c
  have hwr : w.re = β - 5 / 4 := by simp [w, c, line_point_sub_dirichletZeroDiskCenter]
  have hzr : z.re = σ - 5 / 4 := by simp [z, c, line_point_sub_dirichletZeroDiskCenter]
  have he : c + w = (β : ℂ) + (t : ℂ) * Complex.I := by dsimp [w]; ring
  have hβ' : β ≤ 1 := by
    by_contra! hh
    have h := centered_LFunction_ne_zero_of_re_gt_neg_quarter χ t w (by rw [hwr]; linarith)
    rw [he] at h
    exact h hzero
  have hw : w ∈ ball 0 (3 / 8 : ℝ) := by
    rw [mem_ball_zero_iff]
    dsimp [w, c]
    rw [line_point_sub_dirichletZeroDiskCenter, Complex.norm_real, Real.norm_eq_abs]
    apply abs_lt.mpr
    constructor <;> linarith
  have h0 : DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + 0) ≠ 0 := by
    have h := norm_LFunction_zero_disk_center_ge χ t
    rw [add_zero]
    exact norm_pos_iff.mp (by linarith)
  have hp := one_div_re_gap_le_diskZeroPoleSum_re (κ := -(1 / 4 : ℝ))
    (by norm_num : (0 : ℝ) < 3 / 8) (primitive_centered_LFunction_analytic hq hχ t) h0
    (fun u _ hu => centered_LFunction_ne_zero_of_re_gt_neg_quarter χ t u hu)
    (z := z) (by rw [hzr]; linarith) hw
    (by change DirichletCharacter.LFunction χ (c + w) = 0; rw [he]; exact hzero)
    (by simp [w, z, c, line_point_sub_dirichletZeroDiskCenter])
  rw [hzr, hwr, show σ - 5 / 4 - (β - 5 / 4) = σ - β by ring] at hp
  exact hp
theorem primitive_LFunction_logDeriv_re_ge_single_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (σ β t : ℝ)
    (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) (hβ : 7 / 8 < β)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + (t : ℂ) * Complex.I) = 0) :
    1 / (σ - β) - 60000 * Real.log ((q : ℝ) * (|t| + 2)) ≤
      (deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
  have he : dirichletZeroDiskCenter t +
      ((σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t) =
      (σ : ℂ) + (t : ℂ) * Complex.I := by ring
  have hne := centered_LFunction_ne_zero_of_re_gt_neg_quarter χ t
    ((σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t)
    (by rw [line_point_sub_dirichletZeroDiskCenter, Complex.ofReal_re]; linarith)
  rw [he] at hne
  have hb := norm_LFunction_logDeriv_sub_local_zero_poles_le_log hq hχ t _
    (norm_line_point_sub_dirichletZeroDiskCenter_le hσ hσ' t) hne
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  rw [Complex.sub_re] at hr
  have hp := primitive_LFunction_local_zero_poles_re_ge_single hq hχ σ β t hσ hβ hzero
  linarith
end Chen

end

/-! ## ChenTheorem.Lemma6.LFunctionChangeLevelLogDerivative -/

section

open Set Filter
open scoped Topology

namespace Chen
theorem logDeriv_LFunction_changeLevel {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d ∣ q) (χ : DirichletCharacter ℂ d) (s : ℂ) (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.LFunction (χ.changeLevel hdq)) s =
      logDeriv (DirichletCharacter.LFunction χ) s +
      logDeriv (fun z => ∏ p ∈ q.primeFactors, dirichletEulerFactor χ p z) s := by
  have hsne : s ≠ 1 := by intro he; rw [he] at hs; norm_num at hs
  have he : DirichletCharacter.LFunction (χ.changeLevel hdq) =ᶠ[𝓝 s]
      (fun z => DirichletCharacter.LFunction χ z *
        ∏ p ∈ q.primeFactors, dirichletEulerFactor χ p z) := by
    filter_upwards [isOpen_ne.mem_nhds hsne] with z hz
    exact DirichletCharacter.LFunction_changeLevel hdq χ (Or.inr hz)
  have hpne : (∏ p ∈ q.primeFactors, dirichletEulerFactor χ p s) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact dirichletEulerFactor_ne_zero χ (Nat.prime_of_mem_primeFactors hp).two_le s hs.le
  have hpd : DifferentiableAt ℂ
      (fun z => ∏ p ∈ q.primeFactors, dirichletEulerFactor χ p z) s := by
    exact DifferentiableAt.fun_finsetProd (fun p hp =>
      (hasDerivAt_dirichletEulerFactor χ (Nat.pos_of_mem_primeFactors hp).ne' s).differentiableAt)
  calc
    _ = logDeriv (fun z => DirichletCharacter.LFunction χ z *
        ∏ p ∈ q.primeFactors, dirichletEulerFactor χ p z) s := by
      simp only [logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
    _ = _ := logDeriv_mul s
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hsne) hs.le) hpne
      (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hsne)) hpd
theorem norm_logDeriv_LFunction_changeLevel_sub_le {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d ∣ q) (χ : DirichletCharacter ℂ d) (s : ℂ) (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunction (χ.changeLevel hdq)) s -
      logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ Real.log q := by
  rw [logDeriv_LFunction_changeLevel hdq χ s hs, add_sub_cancel_left]
  exact norm_logDeriv_dirichletEulerProduct_le χ q (Nat.pos_of_ne_zero (NeZero.ne q)) s hs.le

end Chen

end

/-! ## ChenTheorem.Lemma6.NonprincipalLogDerivativeBound -/

section

namespace Chen
theorem nonprincipal_LFunction_logDeriv_re_ge {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (σ t : ℝ)
    (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) :
    -(60001 * Real.log ((q : ℝ) * (|t| + 2))) ≤
      (deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hdne : χ.conductor ≠ 1 := by
    intro he
    exact hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr he)
  have hd : 2 ≤ χ.conductor := by have := χ.conductor_ne_zero; omega
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hdq : χ.conductor ≤ q := Nat.le_of_dvd hq χ.conductor_dvd_level
  have hp := primitive_LFunction_logDeriv_re_ge hd χ.primitiveCharacter_isPrimitive σ t hσ hσ'
  have he := norm_logDeriv_LFunction_changeLevel_sub_le χ.conductor_dvd_level
    χ.primitiveCharacter ((σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using hσ)
  rw [χ.changeLevel_primitiveCharacter] at he
  have her := (abs_le.mp ((Complex.abs_re_le_norm _).trans he)).1
  rw [Complex.sub_re] at her
  simp only [logDeriv_apply] at her
  have hdR : (0 : ℝ) < χ.conductor := by exact_mod_cast (by omega : 0 < χ.conductor)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hheight : 0 < |t| + 2 := by positivity
  have hl : Real.log ((χ.conductor : ℝ) * (|t| + 2)) ≤
      Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_le_log (mul_pos hdR hheight)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdq) hheight.le
  have hlq : Real.log q ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_le_log hqR
    nlinarith [abs_nonneg t]
  linarith
end Chen

end

/-! ## ChenTheorem.Lemma6.RealCharacterZeroPair -/

section

open Set Metric ComplexConjugate

namespace Chen
theorem real_conjugate_pole_pair_re (σ β t : ℝ) :
    (1 / ((σ : ℂ) - ((β : ℂ) + (t : ℂ) * Complex.I))).re +
    (1 / ((σ : ℂ) - ((β : ℂ) - (t : ℂ) * Complex.I))).re =
      2 * (σ - β) / ((σ - β) ^ 2 + t ^ 2) := by
  simp only [Complex.div_re, Complex.one_re, Complex.one_im, Complex.normSq_apply,
    Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im,
    Complex.mul_im, zero_mul, mul_zero, sub_zero, add_zero, zero_add, mul_one,
    zero_sub, neg_neg, neg_mul_neg, zero_div, one_mul]
  ring
theorem norm_near_real_zero_shift_lt {β t : ℝ} (hβ : 15 / 16 < β) (hβ' : β ≤ 1)
    (ht : |t| ≤ 1 / 32) :
    ‖(β : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter 0‖ < 3 / 8 := by
  have he : (β : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter 0 =
      ((β - 5 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    simp [dirichletZeroDiskCenter]; ring
  rw [he]
  apply lt_of_le_of_lt (norm_add_le _ _) _
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, abs_of_neg (by linarith : β - 5 / 4 < 0)]
  linarith
/-- A nonreal zero of a primitive real character near 1 contributes together
with its conjugate when the logarithmic derivative is evaluated on the real axis. -/
theorem primitive_real_LFunction_logDeriv_re_ge_zero_pair {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1)
    (σ β t : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) (hβ : 15 / 16 < β)
    (ht : |t| ≤ 1 / 32) (htne : t ≠ 0)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + (t : ℂ) * Complex.I) = 0) :
    2 * (σ - β) / ((σ - β) ^ 2 + t ^ 2) - 60000 * Real.log ((q : ℝ) * 2) ≤
      (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re := by
  have hχne : χ ≠ 1 := by
    intro he
    have hcond := DirichletCharacter.eq_one_iff_conductor_eq_one.mp he
    rw [DirichletCharacter.isPrimitive_def] at hχ
    omega
  have hβ' : β ≤ 1 := by
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; have := congrArg Complex.re he; simp at this; linarith))
      (by simpa using hh.le)) hzero
  let c := dirichletZeroDiskCenter 0
  let w₁ := (β : ℂ) + (t : ℂ) * Complex.I - c
  let w₂ := (β : ℂ) - (t : ℂ) * Complex.I - c
  let z := (σ : ℂ) - c
  have hw₁ : w₁ ∈ ball 0 (3 / 8) := by
    rw [mem_ball_zero_iff]
    exact norm_near_real_zero_shift_lt hβ hβ' ht
  have hw₂ : w₂ ∈ ball 0 (3 / 8) := by
    rw [mem_ball_zero_iff]
    convert norm_near_real_zero_shift_lt hβ hβ' (t := -t) (by simpa using ht) using 1
    simp [w₂, c, sub_eq_add_neg]
  have hf₁ : DirichletCharacter.LFunction χ (c + w₁) = 0 := by
    have he : c + w₁ = (β : ℂ) + (t : ℂ) * Complex.I := by dsimp [w₁]; ring
    rw [he]; exact hzero
  have hf₂ : DirichletCharacter.LFunction χ (c + w₂) = 0 := by
    have he : c + w₂ = conj ((β : ℂ) + (t : ℂ) * Complex.I) := by
      dsimp [w₂]; simp; ring
    rw [he]
    exact real_character_conjugate_zero χ hχne hsq hzero
  have hne : w₁ ≠ w₂ := by
    intro he
    have him := congrArg Complex.im he
    simp [w₁, w₂, c, dirichletZeroDiskCenter] at him
    exact htne (by linarith)
  have h0 : DirichletCharacter.LFunction χ (c + 0) ≠ 0 := by
    exact centered_LFunction_ne_zero_of_re_gt_neg_quarter χ 0 0 (by norm_num)
  have hp := pair_re_zero_poles_le_diskZeroPoleSum_re (κ := -(1 / 4 : ℝ))
    (by norm_num : (0 : ℝ) < 3 / 8) (primitive_centered_LFunction_analytic hq hχ 0) h0
    (fun u _ hu => centered_LFunction_ne_zero_of_re_gt_neg_quarter χ 0 u hu)
    (z := z) (by dsimp [z, c]; simp [dirichletZeroDiskCenter]; linarith)
    hw₁ hw₂ hf₁ hf₂ hne
  have he₁ : z - w₁ = (σ : ℂ) - ((β : ℂ) + (t : ℂ) * Complex.I) := by dsimp [z, w₁]; ring
  have he₂ : z - w₂ = (σ : ℂ) - ((β : ℂ) - (t : ℂ) * Complex.I) := by dsimp [z, w₂]; ring
  rw [he₁, he₂, real_conjugate_pole_pair_re] at hp
  have hsne : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχne) (by simpa using hσ.le)
  have hb := norm_LFunction_logDeriv_sub_local_zero_poles_le_log hq hχ 0 (σ : ℂ)
    (by simpa using norm_line_point_sub_dirichletZeroDiskCenter_le hσ hσ' 0) hsne
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  simp only [Complex.sub_re, abs_zero, zero_add] at hr
  change -(60000 * Real.log ((q : ℝ) * 2)) ≤
    (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re -
      (diskZeroPoleSum (fun w => DirichletCharacter.LFunction χ (c + w)) (3 / 8) z).re at hr
  linarith
end Chen

end

/-! ## ChenTheorem.Lemma6.ZeroFreeLogScale -/

section

namespace Chen
/-- The logarithm in the disk estimate is linear in the requested
conductor-height scale; the large growth bound enters only through a logarithm. -/
theorem zeroFreeDisk_log_growth_le_scale (N : ℕ) (cH cS : ℝ)
    (hcH : 0 < cH) (hcS : 0 < cS) (q : ℕ) (hq : 2 ≤ q) (t : ℝ)
    (hsmall : primitiveZeroFreeWidthAt N cH cS q t ≤ 1 / 4) :
    Real.log (48 * Real.sqrt q * Real.log (2 * q) *
      (‖zeroFreeDiskCenter (primitiveZeroFreeWidthAt N cH cS q t) t‖ +
        primitiveZeroFreeWidthAt N cH cS q t) / primitiveZeroFreeWidthAt N cH cS q t + 1) ≤
      (100 + (1 / cH + 1 / cS)) * primitiveZeroFreeScaleAt N q t := by
  let R := primitiveZeroFreeWidthAt N cH cS q t
  let A : ℝ := (q : ℝ) * (|t| + 2)
  let H := primitiveZeroFreeScaleAt N q t
  let K := 1 / cH + 1 / cS
  have hR : 0 < R := primitiveZeroFreeWidthAt_pos (N := N) hcH hcS hq t
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hA : 4 ≤ A := by dsimp [A]; nlinarith [abs_nonneg t]
  have hqA : (q : ℝ) ≤ A := by dsimp [A]; nlinarith [abs_nonneg t]
  have hcenter : ‖zeroFreeDiskCenter R t‖ + R ≤ A := by
    apply (zeroFreeDiskCenter_norm_add_radius_le R t hR hsmall).trans
    dsimp [A]
    nlinarith [abs_nonneg t]
  have hsqrt : Real.sqrt (q : ℝ) ≤ A := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg q)
    have hn := Real.sqrt_nonneg (q : ℝ)
    nlinarith
  have hlog : Real.log (2 * (q : ℝ)) ≤ 2 * A := by
    have hl := Real.log_le_self (by positivity : (0 : ℝ) ≤ 2 * q)
    linarith
  have hlogpos : 0 < Real.log (2 * (q : ℝ)) := Real.log_pos (by linarith)
  have hnum : 48 * Real.sqrt q * Real.log (2 * q) * (‖zeroFreeDiskCenter R t‖ + R) ≤ 96 * A ^ 3 := by
    calc
      _ ≤ 48 * A * (2 * A) * A := by gcongr
      _ = _ := by ring
  have hunit : 1 ≤ A ^ 3 / R := by
    apply (le_div_iff₀ hR).mpr
    have hpow : 1 ≤ A ^ 3 := one_le_pow₀ (by linarith : 1 ≤ A)
    change R ≤ 1 / 4 at hsmall
    linarith
  have hinside : 48 * Real.sqrt q * Real.log (2 * q) * (‖zeroFreeDiskCenter R t‖ + R) / R + 1 ≤
      97 * A ^ 3 / R := by
    have hd := div_le_div_of_nonneg_right hnum hR.le
    simp only [mul_div_assoc] at hd ⊢
    nlinarith
  have hinsidepos : 0 < 48 * Real.sqrt q * Real.log (2 * q) * (‖zeroFreeDiskCenter R t‖ + R) / R + 1 := by positivity
  have hlogbound := Real.log_le_log hinsidepos hinside
  have heq : Real.log (97 * A ^ 3 / R) = Real.log 97 + 3 * Real.log A + Real.log (1 / R) := by
    rw [Real.log_div (by positivity) hR.ne', Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      Real.log_div one_ne_zero hR.ne', Real.log_one]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [heq] at hlogbound
  have h97 : Real.log 97 ≤ (97 : ℝ) := Real.log_le_self (by norm_num)
  have hlogR : Real.log (1 / R) ≤ 1 / R := Real.log_le_self (by positivity)
  have hinv : 1 / R ≤ K * H := inv_primitiveZeroFreeWidthAt_le_scale N cH cS hcH hcS q hq t
  have hL : 0 < Real.log A := primitiveZeroFreeHeightLog_pos hq t
  have hQ : 0 ≤ (q : ℝ) ^ ((1 : ℝ) / N) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hH1 : 1 ≤ H := by dsimp [H, primitiveZeroFreeScaleAt]; linarith
  have hHL : Real.log A ≤ H := by dsimp [H, primitiveZeroFreeScaleAt]; linarith
  change _ ≤ (100 + K) * H
  linarith
end Chen

end

/-! ## ChenTheorem.Lemma6.ZeroFreeLogDerivativeBound -/

section

namespace Chen
/-- The global logarithmic-derivative condition follows from the mixed
nonvanishing region. Its constant depends only on the two region constants. -/
theorem norm_LFunction_logDeriv_le_scale_sq (N : ℕ) (cH cS : ℝ)
    (hcH : 0 < cH) (hcHsmall : cH ≤ 1 / 8) (hcS : 0 < cS)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 2 ≤ q) (hχ : χ.IsPrimitive)
    (hne : ∀ w : ℂ, 1 - primitiveZeroFreeWidthAt N cH cS q w.im < w.re →
      DirichletCharacter.LFunction χ w ≠ 0)
    (s : ℂ) (hs : 1 - primitiveZeroFreeWidthAt N cH cS q s.im / 2 ≤ s.re) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
      (224 * (100 + (1 / cH + 1 / cS)) * (1 / cH + 1 / cS) +
        4 * (1 / cH + 1 / cS) ^ 2) * primitiveZeroFreeScaleAt N q s.im ^ 2 := by
  let R := primitiveZeroFreeWidthAt N cH cS q s.im
  let H := primitiveZeroFreeScaleAt N q s.im
  let K := 1 / cH + 1 / cS
  have hR : 0 < R := primitiveZeroFreeWidthAt_pos (N := N) hcH hcS hq s.im
  have hsmall : R ≤ 1 / 4 := primitiveZeroFreeWidthAt_le_quarter N cH cS hcHsmall q hq s.im
  have hK : 0 < K := by dsimp [K]; positivity
  have hH : 0 < H := by
    have hL := primitiveZeroFreeHeightLog_pos hq s.im
    have hQ := Real.rpow_nonneg (Nat.cast_nonneg q) ((1 : ℝ) / N)
    dsimp [H, primitiveZeroFreeScaleAt]
    linarith
  have hinv : 1 / R ≤ K * H := inv_primitiveZeroFreeWidthAt_le_scale N cH cS hcH hcS q hq s.im
  change _ ≤ (224 * (100 + K) * K + 4 * K ^ 2) * H ^ 2
  by_cases hnear : s.re ≤ 1 + R
  · have hd := norm_LFunction_logDeriv_le_of_mixed_region N cH cS hcH hcS hq hχ hne s hsmall hs hnear
    have hg := zeroFreeDisk_log_growth_le_scale N cH cS hcH hcS q hq s.im hsmall
    apply hd.trans
    calc
      _ ≤ 224 * ((100 + K) * H) / R :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by norm_num)) hR.le
      _ = (224 * ((100 + K) * H)) * (1 / R) := by ring
      _ ≤ (224 * ((100 + K) * H)) * (K * H) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (K * H)]
  · have hgap : 0 < s.re - 1 := by linarith
    have hd := (lemma6_norm_logDeriv_le_majorant χ (by linarith : 1 < s.re)).trans
      (lemma6LogDerivMajorant_le hgap (show s.re = 1 + (s.re - 1) by ring))
    have hdist : 1 / (s.re - 1) ≤ 1 / R := one_div_le_one_div_of_le hR (by linarith)
    have hsq : (1 / (s.re - 1)) ^ 2 ≤ (K * H) ^ 2 :=
      sq_le_sq₀ (by positivity) (by positivity) |>.mpr (hdist.trans hinv)
    apply hd.trans
    rw [show 4 / (s.re - 1) ^ 2 = 4 * (1 / (s.re - 1)) ^ 2 by rw [div_pow, one_pow]; ring]
    have hpos : 0 ≤ 224 * (100 + K) * K * H ^ 2 := by positivity
    nlinarith
end Chen

end

/-! ## ChenTheorem.Lemma6.ZeroFreeRegionAssembly -/

section

namespace Chen

/-- The logarithmic-derivative field of the classical package is redundant:
a mixed nonvanishing region supplies it after reducing the height constant. -/
theorem primitiveZeroFreeRegionDataAt_of_nonvanishing (N : ℕ) (cH cS : ℝ)
    (hcH : 0 < cH) (hcS : 0 < cS)
    (hne : ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
        1 - primitiveZeroFreeWidthAt N cH cS q s.im < s.re →
          DirichletCharacter.LFunction χ s ≠ 0) :
    Nonempty (PrimitiveZeroFreeRegionDataAt N) := by
  let H := min cH (1 / 8)
  let K := 1 / H + 1 / cS
  have hH : 0 < H := lt_min hcH (by norm_num)
  have hHsmall : H ≤ 1 / 8 := min_le_right _ _
  have hK : 0 < K := by dsimp [K]; positivity
  have hnv : ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
        1 - primitiveZeroFreeWidthAt N H cS q s.im < s.re →
          DirichletCharacter.LFunction χ s ≠ 0 := by
    intro q hqInst χ hq hχ s hs
    have hw : primitiveZeroFreeWidthAt N H cS q s.im ≤ primitiveZeroFreeWidthAt N cH cS q s.im :=
      min_le_min (div_le_div_of_nonneg_right (min_le_left _ _) (primitiveZeroFreeHeightLog_pos hq s.im).le) le_rfl
    exact hne q hqInst χ hq hχ s (by linarith)
  refine ⟨{
    cHeight := H
    cSiegel := cS
    cLogDeriv := 224 * (100 + K) * K + 4 * K ^ 2
    cHeight_pos := hH
    cSiegel_pos := hcS
    cLogDeriv_pos := by positivity
    nonvanishing := hnv
    logDeriv_bound := ?_ }⟩
  intro q hqInst χ hq hχ s hs
  exact norm_LFunction_logDeriv_le_scale_sq N H cS hH hHsmall hcS hq hχ
    (hnv q hqInst χ hq hχ) s hs

theorem primitiveZeroFreeRegionData_of_dataAt (data : PrimitiveZeroFreeRegionDataAt 300) :
    Nonempty PrimitiveZeroFreeRegionData := by
  refine ⟨{
    cHeight := data.cHeight
    cSiegel := data.cSiegel
    cLogDeriv := data.cLogDeriv
    cHeight_pos := data.cHeight_pos
    cSiegel_pos := data.cSiegel_pos
    cLogDeriv_pos := data.cLogDeriv_pos
    nonvanishing := ?_
    logDeriv_bound := ?_ }⟩
  · simpa only [primitiveZeroFreeWidth, primitiveZeroFreeWidthAt, Nat.cast_ofNat] using data.nonvanishing
  · simpa only [primitiveZeroFreeWidth, primitiveZeroFreeWidthAt, Nat.cast_ofNat] using data.logDeriv_bound

/-- To finish the zero-free-region package it suffices to prove the mixed
nonvanishing region at each fixed Siegel exponent. The companion derivative
estimate is now a consequence of the proved disk and scale estimates. -/
theorem primitiveZeroFreeRegion_of_nonvanishing
    (h : ∀ N : ℕ, 1 ≤ N → ∃ cH cS : ℝ, 0 < cH ∧ 0 < cS ∧
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
          1 - primitiveZeroFreeWidthAt N cH cS q s.im < s.re →
            DirichletCharacter.LFunction χ s ≠ 0) : PrimitiveZeroFreeRegion := by
  have hdata : ∀ N : ℕ, 1 ≤ N → Nonempty (PrimitiveZeroFreeRegionDataAt N) := by
    intro N hN
    obtain ⟨cH, cS, hcH, hcS, hnv⟩ := h N hN
    exact primitiveZeroFreeRegionDataAt_of_nonvanishing N cH cS hcH hcS hnv
  obtain ⟨data⟩ := hdata 300 (by norm_num)
  exact ⟨primitiveZeroFreeRegionData_of_dataAt data, hdata⟩

end Chen

end

/-! ## ChenTheorem.Lemma6.ZetaRealLogDerivativeBound -/

section

open Set Metric
open scoped Topology

namespace Chen
theorem exists_zeta_real_logDeriv_pole_bound :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + C := by
  obtain ⟨U, hU, B, hB⟩ := riemannZetaLogDerivResidue
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ, max B 1, hδ, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro σ hσ hσδ
  have hsU : (σ : ℂ) ∈ U := by
    apply hδU
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < σ - 1)]
    linarith
  have hsne : (σ : ℂ) ≠ 1 := by
    intro he
    have := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.one_re] at this
    linarith
  have hb := hB (mem_image_of_mem _ (show (σ : ℂ) ∈ U \ {1} from ⟨hsU, hsne⟩))
  change ‖-(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)) - ((σ : ℂ) - 1)⁻¹‖ ≤ B at hb
  have hr := (Complex.re_le_norm _).trans (hb.trans (le_max_left B (1 : ℝ)))
  rw [Complex.sub_re, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_inv, Complex.ofReal_re] at hr
  rw [neg_div]
  rw [one_div]
  linarith
end Chen

end

/-! ## ChenTheorem.Lemma6.NonrealZeroInequality -/

section

namespace Chen
theorem conductor_height_log_double_le {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    Real.log ((q : ℝ) * (|2 * t| + 2)) ≤
      2 * Real.log ((q : ℝ) * (|t| + 2)) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : 0 < (q : ℝ) * (|t| + 2) := by positivity
  have hA : 2 ≤ (q : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ Real.log (((q : ℝ) * (|t| + 2)) ^ 2) := by
      apply Real.log_le_log (by positivity)
      nlinarith [sq_nonneg ((q : ℝ) * (|t| + 2) - 2)]
    _ = _ := by rw [Real.log_pow]; norm_num
theorem primitive_nonreal_zero_inequality {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive)
    (hχsq : χ ^ 2 ≠ 1) (σ β t C : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2)
    (hβ : 7 / 8 < β)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + (t : ℂ) * Complex.I) = 0)
    (hzeta : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤
      1 / (σ - 1) + C) :
    4 / (σ - β) ≤ 3 / (σ - 1) + 3 * C +
      360002 * Real.log ((q : ℝ) * (|t| + 2)) := by
  have h1 := primitive_LFunction_logDeriv_re_ge_single_zero hq hχ σ β t hσ hσ' hβ hzero
  have h2 := nonprincipal_LFunction_logDeriv_re_ge (χ ^ 2) hχsq σ (2 * t) hσ hσ'
  have h3 := Dirichlet_logDeriv_three_four_one_nonneg χ σ t hσ
  norm_num [Complex.add_re, Complex.mul_re, neg_div] at h3 hzeta
  have h4 := conductor_height_log_double_le hq t
  norm_num at h1 h2 h4 ⊢
  simp only [div_eq_mul_inv]
  linarith
end Chen

end

/-! ## ChenTheorem.Lemma6.NonrealZeroFreeRegion -/

section

namespace Chen
theorem four_div_gap_contradiction {x y D : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : 8 * y ≤ 9 * x) (hDx : D * x ≤ 1 / 4)
    (hineq : 4 / y ≤ 3 / x + D) : False := by
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hy).mp hineq) hx.le
  have he : (3 / x + D) * y * x = 3 * y + (D * x) * y := by
    calc
      _ = (3 / x * x) * y + (D * x) * y := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hx.ne']
  rw [he] at hh
  have hb := mul_le_mul_of_nonneg_right hDx hy.le
  nlinarith
/-- A uniform classical logarithmic zero-free region for primitive characters
whose square is nonprincipal. Real characters, including exceptional real zeros,
are deliberately not covered by this theorem. -/
theorem exists_primitive_nonreal_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 ≠ 1 → ∀ s : ℂ,
      1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨δ, C, hδ, hC, hzeta⟩ := exists_zeta_real_logDeriv_pole_bound
  let B : ℝ := 4 * C + 360002
  have hB : 0 < B := by dsimp [B]; positivity
  let a : ℝ := min (δ / 4) (min (1 / 16) (1 / (4 * B)))
  have ha : 0 < a := by dsimp [a]; positivity
  have haδ : a ≤ δ / 4 := min_le_left _ _
  have ha16 : a ≤ 1 / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have haB : a * B ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * B)).mp
      (show a ≤ 1 / (4 * B) from (min_le_right _ _).trans (min_le_right _ _))
    nlinarith
  refine ⟨a / 8, by positivity, ?_⟩
  intro q inst χ hq hχ hχsq s hs hzero
  let L : ℝ := Real.log ((q : ℝ) * (|s.im| + 2))
  have hL : 3 / 4 ≤ L := conductor_height_log_ge_threeQuarters q hq s.im
  have hLpos : 0 < L := by linarith
  have hβ : s.re ≤ 1 := by
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; rw [he] at hh; norm_num at hh)) hh.le) hzero
  let x : ℝ := a / L
  let σ : ℝ := 1 + x
  let y : ℝ := σ - s.re
  let D : ℝ := 3 * C + 360002 * L
  have hx : 0 < x := div_pos ha hLpos
  have hxL : x * L = a := div_mul_cancel₀ _ hLpos.ne'
  have hxδ : x < δ := by
    apply (div_lt_iff₀ hLpos).mpr
    nlinarith
  have hx16 : x ≤ 1 / 12 := by
    apply (div_le_iff₀ hLpos).mpr
    linarith
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hσ' : σ ≤ 3 / 2 := by dsimp [σ]; linarith
  have hσδ : σ < 1 + δ := by dsimp [σ]; linarith
  have hy : 0 < y := by dsimp [y]; linarith
  have hquot : (a / 8) / L = x / 8 := by dsimp [x]; ring
  change 1 - (a / 8) / L < s.re at hs
  rw [hquot] at hs
  have hxy : 8 * y ≤ 9 * x := by dsimp [y, σ]; linarith
  have hβ' : 7 / 8 < s.re := by linarith
  have hD : D ≤ B * L := by dsimp [D, B]; nlinarith
  have hDx : D * x ≤ 1 / 4 := by
    calc
      _ ≤ (B * L) * x := mul_le_mul_of_nonneg_right hD hx.le
      _ = B * a := by rw [mul_assoc, mul_comm L x, hxL]
      _ ≤ _ := by nlinarith [haB]
  have hz : DirichletCharacter.LFunction χ
      ((s.re : ℂ) + (s.im : ℂ) * Complex.I) = 0 := by
    rw [Complex.re_add_im]
    exact hzero
  have hi := primitive_nonreal_zero_inequality hq hχ hχsq σ s.re s.im C
    hσ hσ' hβ' hz (hzeta σ hσ hσδ)
  change 4 / y ≤ 3 / (σ - 1) + 3 * C + 360002 * L at hi
  have hσx : σ - 1 = x := by dsimp [σ]; ring
  rw [hσx] at hi
  exact four_div_gap_contradiction hx hy hxy hDx (by dsimp [D]; linarith [hi])
end Chen

end

/-! ## ChenTheorem.Lemma6.PrincipalLogDerivativeBound -/

section

open Set Metric
open scoped Topology

namespace Chen
theorem norm_principal_logDeriv_sub_zeta_le {q : ℕ} [NeZero q]
    (s : ℂ) (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s -
      logDeriv riemannZeta s‖ ≤ Real.log q := by
  simpa only [DirichletCharacter.changeLevel_one, DirichletCharacter.LFunction_modOne_eq]
    using norm_logDeriv_LFunction_changeLevel_sub_le (Nat.one_dvd q)
      (1 : DirichletCharacter ℂ 1) s hs
theorem exists_zeta_complex_logDeriv_pole_bound :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ s : ℂ, ‖s - 1‖ < δ → s ≠ 1 →
      ‖logDeriv riemannZeta s + (s - 1)⁻¹‖ ≤ C := by
  obtain ⟨U, hU, B, hB⟩ := riemannZetaLogDerivResidue
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ, max B 1, hδ, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro s hs hsne
  have hsU : s ∈ U := hδU (by simpa only [mem_ball, dist_eq_norm] using hs)
  have hb := hB (mem_image_of_mem _ (show s ∈ U \ {1} from ⟨hsU, hsne⟩))
  change ‖-(deriv riemannZeta s / riemannZeta s) - (s - 1)⁻¹‖ ≤ B at hb
  have he : -(deriv riemannZeta s / riemannZeta s) - (s - 1)⁻¹ =
      -(logDeriv riemannZeta s + (s - 1)⁻¹) := by rw [logDeriv_apply]; ring
  rw [he, norm_neg] at hb
  exact hb.trans (le_max_left _ _)
theorem exists_principal_complex_logDeriv_pole_bound :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (q : ℕ) [NeZero q] (s : ℂ),
      1 < s.re → ‖s - 1‖ < δ →
      ‖logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s +
        (s - 1)⁻¹‖ ≤ C + Real.log q := by
  obtain ⟨δ, C, hδ, hC, hz⟩ := exists_zeta_complex_logDeriv_pole_bound
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro q inst s hs hsδ
  have hsne : s ≠ 1 := by intro he; rw [he] at hs; norm_num at hs
  have h1 := norm_principal_logDeriv_sub_zeta_le (q := q) s hs
  have h2 := hz s hsδ hsne
  calc
    _ = ‖(logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s -
        logDeriv riemannZeta s) + (logDeriv riemannZeta s + (s - 1)⁻¹)‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (by linarith)
end Chen

end

/-! ## ChenTheorem.Lemma6.RealCharacterZeroInequality -/

section

namespace Chen
theorem principal_logDeriv_re_ge_of_pole_bound {q : ℕ} [NeZero q]
    (s : ℂ) (C : ℝ)
    (hb : ‖logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s +
      (s - 1)⁻¹‖ ≤ C + Real.log q) :
    -((s - 1)⁻¹).re - C - Real.log q ≤
      (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s).re := by
  have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  rw [Complex.add_re] at h
  linarith
theorem primitive_real_zero_inequality {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1)
    (σ β t Cz Cp : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) (hβ : 7 / 8 < β)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + (t : ℂ) * Complex.I) = 0)
    (hzeta : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + Cz)
    (hprincipal : ‖logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
      ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) +
      ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I - 1)⁻¹‖ ≤ Cp + Real.log q) :
    4 / (σ - β) ≤ 3 / (σ - 1) +
      (((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I - 1)⁻¹).re +
      3 * Cz + Cp + 240000 * Real.log ((q : ℝ) * (|t| + 2)) + Real.log q := by
  have h1 := primitive_LFunction_logDeriv_re_ge_single_zero hq hχ σ β t hσ hσ' hβ hzero
  have h2 := principal_logDeriv_re_ge_of_pole_bound _ Cp hprincipal
  have h3 := Dirichlet_logDeriv_three_four_one_nonneg χ σ t hσ
  rw [hsq] at h3
  simp only [logDeriv_apply] at h2
  norm_num [Complex.add_re, Complex.mul_re, neg_div] at h3 hzeta
  norm_num at h1 h2 ⊢
  simp only [div_eq_mul_inv] at h1 h2 h3 hzeta ⊢
  linarith
theorem real_character_logDeriv_real_axis_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (σ Cz Cp : ℝ) (hσ : 1 < σ)
    (hzeta : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + Cz)
    (hprincipal : ‖logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
      (σ : ℂ) + ((σ : ℂ) - 1)⁻¹‖ ≤ Cp + Real.log q) :
    (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re ≤
      1 / (σ - 1) + (3 * Cz + Cp + Real.log q) / 4 := by
  have h2 := principal_logDeriv_re_ge_of_pole_bound (σ : ℂ) Cp hprincipal
  have h3 := Dirichlet_logDeriv_three_four_one_nonneg χ σ 0 hσ
  rw [hsq] at h3
  have he : (((σ : ℂ) - 1)⁻¹).re = 1 / (σ - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  rw [he] at h2
  simp only [logDeriv_apply] at h2 ⊢
  norm_num [Complex.add_re, Complex.mul_re, neg_div] at h3 hzeta
  norm_num at h2 ⊢
  simp only [div_eq_mul_inv] at h2 h3 hzeta ⊢
  norm_num only
  linarith
end Chen

end

/-! ## ChenTheorem.Lemma6.RealZeroBox -/

section

namespace Chen
theorem conjugate_pair_gap_contradiction {x y t D : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) (hyx : y ≤ 9 * x / 8) (ht : |t| ≤ x / 8)
    (hDx : D * x ≤ 1 / 4)
    (hi : 2 * y / (y ^ 2 + t ^ 2) ≤ 1 / x + D) : False := by
  have hy : 0 < y := hx.trans_le hxy
  have hden : 0 < y ^ 2 + t ^ 2 := by positivity
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hden).mp hi) hx.le
  have he : (1 / x + D) * (y ^ 2 + t ^ 2) * x =
      (y ^ 2 + t ^ 2) + (D * x) * (y ^ 2 + t ^ 2) := by
    calc
      _ = (1 / x * x) * (y ^ 2 + t ^ 2) + (D * x) * (y ^ 2 + t ^ 2) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hx.ne', one_mul]
  rw [he] at hh
  have hb := mul_le_mul_of_nonneg_right hDx hden.le
  have hy2 : y ^ 2 ≤ 81 * x ^ 2 / 64 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (show 0 ≤ 9 * x / 8 + y by positivity)]
  have ht2 : t ^ 2 ≤ x ^ 2 / 64 := by
    have h := abs_le.mp ht
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (show 0 ≤ x / 8 + t by linarith [h.1])]
  have hxy2 := mul_le_mul_of_nonneg_right hxy hx.le
  nlinarith
/-- Any zero of a primitive real character in a uniform logarithmic box
around 1 is real. This leaves open the existence and distance of an exceptional real zero. -/
theorem exists_primitive_real_zero_box_im_eq_zero :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → ∀ s : ℂ,
      1 - c / Real.log ((q : ℝ) * 2) < s.re →
      |s.im| ≤ c / Real.log ((q : ℝ) * 2) →
      DirichletCharacter.LFunction χ s = 0 → s.im = 0 := by
  obtain ⟨δz, Cz, hδz, hCz, hzeta⟩ := exists_zeta_real_logDeriv_pole_bound
  obtain ⟨δp, Cp, hδp, hCp, hprincipal⟩ := exists_principal_complex_logDeriv_pole_bound
  let δ := min δz δp
  have hδ : 0 < δ := lt_min hδz hδp
  let B : ℝ := Cz + Cp + 60001
  have hB : 0 < B := by dsimp [B]; positivity
  let a : ℝ := min (δ / 4) (min (1 / 8) (1 / (4 * B)))
  have ha : 0 < a := by dsimp [a]; positivity
  have haδ : a ≤ δ / 4 := min_le_left _ _
  have ha8 : a ≤ 1 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have haB : a * B ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * B)).mp
      (show a ≤ 1 / (4 * B) from (min_le_right _ _).trans (min_le_right _ _))
    nlinarith
  refine ⟨a / 8, by positivity, ?_⟩
  intro q inst χ hq hχ hsq s hs ht hzero
  by_contra htne
  let L : ℝ := Real.log ((q : ℝ) * 2)
  have hL : 3 / 4 ≤ L := by simpa [L] using conductor_height_log_ge_threeQuarters q hq 0
  have hLp : 0 < L := by linarith
  let x : ℝ := a / L
  let σ : ℝ := 1 + x
  let y : ℝ := σ - s.re
  let D : ℝ := (3 * Cz + Cp + Real.log q) / 4
  have hx : 0 < x := div_pos ha hLp
  have hxL : x * L = a := div_mul_cancel₀ _ hLp.ne'
  have hxδ : x < δ := by apply (div_lt_iff₀ hLp).mpr; nlinarith
  have hx6 : x ≤ 1 / 6 := by apply (div_le_iff₀ hLp).mpr; linarith
  have hquot : (a / 8) / L = x / 8 := by dsimp [x]; ring
  change 1 - (a / 8) / L < s.re at hs
  change |s.im| ≤ (a / 8) / L at ht
  rw [hquot] at hs ht
  have hβ : s.re ≤ 1 := by
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; rw [he] at hh; norm_num at hh)) hh.le) hzero
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hσ' : σ ≤ 3 / 2 := by dsimp [σ]; linarith
  have hσδ : σ < 1 + δz := by dsimp [σ]; linarith [min_le_left δz δp]
  have hσδp : ‖(σ : ℂ) - 1‖ < δp := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < σ - 1)]
    dsimp [σ]
    linarith [min_le_right δz δp]
  have hpair := primitive_real_LFunction_logDeriv_re_ge_zero_pair hq hχ hsq σ s.re s.im
    hσ hσ' (by linarith) (by linarith) htne
    (by rw [Complex.re_add_im]; exact hzero)
  have hu := real_character_logDeriv_real_axis_le χ hsq σ Cz Cp hσ
    (hzeta σ hσ hσδ) (hprincipal q (σ : ℂ) (by simpa using hσ) hσδp)
  have hlogq : Real.log q ≤ L := by
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < q))
    have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have hD : D + 60000 * L ≤ B * L := by dsimp [D, B]; nlinarith
  have hDx : (D + 60000 * L) * x ≤ 1 / 4 := by
    calc
      _ ≤ (B * L) * x := mul_le_mul_of_nonneg_right hD hx.le
      _ = B * a := by rw [mul_assoc, mul_comm L x, hxL]
      _ ≤ _ := by nlinarith [haB]
  have hxy : x ≤ y := by dsimp [y, σ]; linarith
  have hyx : y ≤ 9 * x / 8 := by dsimp [y, σ]; linarith
  have hi : 2 * y / (y ^ 2 + s.im ^ 2) ≤ 1 / x + (D + 60000 * L) := by
    have he : σ - 1 = x := by dsimp [σ]; ring
    rw [he] at hu
    change 2 * y / (y ^ 2 + s.im ^ 2) - 60000 * L ≤ _ at hpair
    dsimp [D]
    linarith
  exact conjugate_pair_gap_contradiction hx hxy hyx ht hDx hi
end Chen

end

/-! ## ChenTheorem.Lemma6.RealZeroUniquenessTools -/

section

open Set Metric

namespace Chen
theorem primitive_LFunction_logDeriv_re_ge_two_real_zeros {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive)
    (σ β₁ β₂ : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2)
    (hβ₁ : 15 / 16 < β₁) (hβ₂ : 15 / 16 < β₂) (hne : β₁ ≠ β₂)
    (hf₁ : DirichletCharacter.LFunction χ (β₁ : ℂ) = 0)
    (hf₂ : DirichletCharacter.LFunction χ (β₂ : ℂ) = 0) :
    1 / (σ - β₁) + 1 / (σ - β₂) - 60000 * Real.log ((q : ℝ) * 2) ≤
      (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re := by
  have hzero_le : ∀ β : ℝ, DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 := by
    intro β hb
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; have := congrArg Complex.re he; simp at this; linarith))
      (by simpa using hh.le)) hb
  let c := dirichletZeroDiskCenter 0
  let w₁ := (β₁ : ℂ) - c
  let w₂ := (β₂ : ℂ) - c
  let z := (σ : ℂ) - c
  have hw₁ : w₁ ∈ ball 0 (3 / 8) := by
    rw [mem_ball_zero_iff]
    simpa [w₁, c] using norm_near_real_zero_shift_lt hβ₁ (hzero_le β₁ hf₁) (t := 0) (by norm_num)
  have hw₂ : w₂ ∈ ball 0 (3 / 8) := by
    rw [mem_ball_zero_iff]
    simpa [w₂, c] using norm_near_real_zero_shift_lt hβ₂ (hzero_le β₂ hf₂) (t := 0) (by norm_num)
  have hf₁' : DirichletCharacter.LFunction χ (c + w₁) = 0 := by
    have he : c + w₁ = (β₁ : ℂ) := by dsimp [w₁]; ring
    rw [he]; exact hf₁
  have hf₂' : DirichletCharacter.LFunction χ (c + w₂) = 0 := by
    have he : c + w₂ = (β₂ : ℂ) := by dsimp [w₂]; ring
    rw [he]; exact hf₂
  have hne' : w₁ ≠ w₂ := by
    intro he
    have h := congrArg Complex.re he
    simp [w₁, w₂] at h
    exact hne (by linarith)
  have h0 : DirichletCharacter.LFunction χ (c + 0) ≠ 0 :=
    centered_LFunction_ne_zero_of_re_gt_neg_quarter χ 0 0 (by norm_num)
  have hp := pair_re_zero_poles_le_diskZeroPoleSum_re (κ := -(1 / 4 : ℝ))
    (by norm_num : (0 : ℝ) < 3 / 8) (primitive_centered_LFunction_analytic hq hχ 0) h0
    (fun u _ hu => centered_LFunction_ne_zero_of_re_gt_neg_quarter χ 0 u hu)
    (z := z) (by dsimp [z, c]; simp [dirichletZeroDiskCenter]; linarith)
    hw₁ hw₂ hf₁' hf₂' hne'
  have he₁ : z - w₁ = ((σ - β₁ : ℝ) : ℂ) := by dsimp [z, w₁]; push_cast; ring
  have he₂ : z - w₂ = ((σ - β₂ : ℝ) : ℂ) := by dsimp [z, w₂]; push_cast; ring
  rw [he₁, he₂, ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_div,
    Complex.ofReal_re, Complex.ofReal_re] at hp
  have hsne : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; have := congrArg Complex.re he; simp at this; linarith))
      (by simpa using hσ.le)
  have hb := norm_LFunction_logDeriv_sub_local_zero_poles_le_log hq hχ 0 (σ : ℂ)
    (by simpa using norm_line_point_sub_dirichletZeroDiskCenter_le hσ hσ' 0) hsne
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  simp only [Complex.sub_re, abs_zero, zero_add] at hr
  change -(60000 * Real.log ((q : ℝ) * 2)) ≤
    (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re -
      (diskZeroPoleSum (fun w => DirichletCharacter.LFunction χ (c + w)) (3 / 8) z).re at hr
  linarith
theorem two_real_zero_gaps_contradiction {x y₁ y₂ D : ℝ} (hx : 0 < x)
    (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (h₁ : y₁ ≤ 9 * x / 8) (h₂ : y₂ ≤ 9 * x / 8)
    (hDx : D * x ≤ 1 / 4) (hi : 1 / y₁ + 1 / y₂ ≤ 1 / x + D) : False := by
  have hden : 0 < 9 * x := by positivity
  have hb₁ : 8 / (9 * x) ≤ 1 / y₁ := by
    apply (div_le_div_iff₀ hden hy₁).mpr
    nlinarith
  have hb₂ : 8 / (9 * x) ≤ 1 / y₂ := by
    apply (div_le_div_iff₀ hden hy₂).mpr
    nlinarith
  have hh : 16 / (9 * x) ≤ 1 / x + D := by
    calc
      _ = 8 / (9 * x) + 8 / (9 * x) := by ring
      _ ≤ 1 / y₁ + 1 / y₂ := add_le_add hb₁ hb₂
      _ ≤ _ := hi
  have hh' := (div_le_iff₀ hden).mp hh
  have he : (1 / x + D) * (9 * x) = 9 + 9 * (D * x) := by
    calc
      _ = 9 * (1 / x * x) + 9 * (D * x) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hx.ne', mul_one]
  rw [he] at hh'
  linarith
theorem exists_real_character_logDeriv_real_axis_bound :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ^ 2 = 1 → ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re ≤
        1 / (σ - 1) + C + Real.log q / 4 := by
  obtain ⟨δz, Cz, hδz, hCz, hzeta⟩ := exists_zeta_real_logDeriv_pole_bound
  obtain ⟨δp, Cp, hδp, hCp, hprincipal⟩ := exists_principal_complex_logDeriv_pole_bound
  refine ⟨min δz δp, (3 * Cz + Cp) / 4, lt_min hδz hδp, by positivity, ?_⟩
  intro q inst χ hsq σ hσ hσδ
  have hz : σ < 1 + δz := by linarith [min_le_left δz δp]
  have hp : ‖(σ : ℂ) - 1‖ < δp := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < σ - 1)]
    linarith [min_le_right δz δp]
  have h := real_character_logDeriv_real_axis_le χ hsq σ Cz Cp hσ (hzeta σ hσ hz)
    (hprincipal q (σ : ℂ) (by simpa using hσ) hp)
  linarith
end Chen

end

/-! ## ChenTheorem.Lemma6.RealMultipleZeroBound -/

section

open Set Metric

namespace Chen
theorem primitive_LFunction_logDeriv_re_ge_multiple_real_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive)
    (σ β : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) (hβ : 15 / 16 < β)
    (hf : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hdf : deriv (DirichletCharacter.LFunction χ) (β : ℂ) = 0) :
    2 / (σ - β) - 60000 * Real.log ((q : ℝ) * 2) ≤
      (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re := by
  have hβ' : β ≤ 1 := by
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; have := congrArg Complex.re he; simp at this; linarith))
      (by simpa using hh.le)) hf
  let c := dirichletZeroDiskCenter 0
  let w := (β : ℂ) - c
  let z := (σ : ℂ) - c
  have hw : w ∈ ball 0 (3 / 8) := by
    rw [mem_ball_zero_iff]
    simpa [w, c] using norm_near_real_zero_shift_lt hβ hβ' (t := 0) (by norm_num)
  have he : c + w = (β : ℂ) := by dsimp [w]; ring
  have hf' : DirichletCharacter.LFunction χ (c + w) = 0 := by rw [he]; exact hf
  have hdf' : deriv (fun u => DirichletCharacter.LFunction χ (c + u)) w = 0 := by
    rw [deriv_comp_const_add, he]
    exact hdf
  have h0 : DirichletCharacter.LFunction χ (c + 0) ≠ 0 :=
    centered_LFunction_ne_zero_of_re_gt_neg_quarter χ 0 0 (by norm_num)
  have hp := two_div_re_gap_le_diskZeroPoleSum_re_of_zero_deriv (κ := -(1 / 4 : ℝ))
    (by norm_num : (0 : ℝ) < 3 / 8) (primitive_centered_LFunction_analytic hq hχ 0) h0
    (fun u _ hu => centered_LFunction_ne_zero_of_re_gt_neg_quarter χ 0 u hu)
    (z := z) (by dsimp [z, c]; simp [dirichletZeroDiskCenter]; linarith)
    hw hf' hdf' (by simp [w, z, c, dirichletZeroDiskCenter])
  have hre : z.re - w.re = σ - β := by simp [z, w]
  rw [hre] at hp
  have hsne : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; have := congrArg Complex.re he; simp at this; linarith))
      (by simpa using hσ.le)
  have hb := norm_LFunction_logDeriv_sub_local_zero_poles_le_log hq hχ 0 (σ : ℂ)
    (by simpa using norm_line_point_sub_dirichletZeroDiskCenter_le hσ hσ' 0) hsne
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  simp only [Complex.sub_re, abs_zero, zero_add] at hr
  change -(60000 * Real.log ((q : ℝ) * 2)) ≤
    (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re -
      (diskZeroPoleSum (fun u => DirichletCharacter.LFunction χ (c + u)) (3 / 8) z).re at hr
  linarith
end Chen

end

/-! ## ChenTheorem.Lemma6.RealZeroUniqueness -/

section

namespace Chen
theorem exists_primitive_real_zero_unique :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → ∀ β₁ β₂ : ℝ,
      1 - c / Real.log ((q : ℝ) * 2) < β₁ →
      1 - c / Real.log ((q : ℝ) * 2) < β₂ →
      DirichletCharacter.LFunction χ (β₁ : ℂ) = 0 →
      DirichletCharacter.LFunction χ (β₂ : ℂ) = 0 → β₁ = β₂ := by
  obtain ⟨δ, C, hδ, hC, hu⟩ := exists_real_character_logDeriv_real_axis_bound
  let B : ℝ := 2 * C + 60001
  have hB : 0 < B := by dsimp [B]; positivity
  let a : ℝ := min (δ / 4) (min (1 / 8) (1 / (4 * B)))
  have ha : 0 < a := by dsimp [a]; positivity
  have haδ : a ≤ δ / 4 := min_le_left _ _
  have ha8 : a ≤ 1 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have haB : a * B ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * B)).mp
      (show a ≤ 1 / (4 * B) from (min_le_right _ _).trans (min_le_right _ _))
    nlinarith
  refine ⟨a / 8, by positivity, ?_⟩
  intro q inst χ hq hχ hsq β₁ β₂ hβ₁ hβ₂ hf₁ hf₂
  by_contra hne
  let L : ℝ := Real.log ((q : ℝ) * 2)
  have hL : 3 / 4 ≤ L := by simpa [L] using conductor_height_log_ge_threeQuarters q hq 0
  have hLp : 0 < L := by linarith
  let x : ℝ := a / L
  let σ : ℝ := 1 + x
  let y₁ : ℝ := σ - β₁
  let y₂ : ℝ := σ - β₂
  let D : ℝ := C + Real.log q / 4 + 60000 * L
  have hx : 0 < x := div_pos ha hLp
  have hxL : x * L = a := div_mul_cancel₀ _ hLp.ne'
  have hxδ : x < δ := by apply (div_lt_iff₀ hLp).mpr; nlinarith
  have hx6 : x ≤ 1 / 6 := by apply (div_le_iff₀ hLp).mpr; linarith
  have hquot : (a / 8) / L = x / 8 := by dsimp [x]; ring
  change 1 - (a / 8) / L < β₁ at hβ₁
  change 1 - (a / 8) / L < β₂ at hβ₂
  rw [hquot] at hβ₁ hβ₂
  have hzero_le : ∀ β : ℝ, DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 := by
    intro β hb
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; have := congrArg Complex.re he; simp at this; linarith))
      (by simpa using hh.le)) hb
  have hb₁ := hzero_le β₁ hf₁
  have hb₂ := hzero_le β₂ hf₂
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hσ' : σ ≤ 3 / 2 := by dsimp [σ]; linarith
  have hσδ : σ < 1 + δ := by dsimp [σ]; linarith
  have hpair := primitive_LFunction_logDeriv_re_ge_two_real_zeros hq hχ σ β₁ β₂
    hσ hσ' (by linarith) (by linarith) hne hf₁ hf₂
  have hup := hu q χ hsq σ hσ hσδ
  have hlogq : Real.log q ≤ L := by
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < q))
    have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have hD : D ≤ B * L := by dsimp [D, B]; nlinarith
  have hDx : D * x ≤ 1 / 4 := by
    calc
      _ ≤ (B * L) * x := mul_le_mul_of_nonneg_right hD hx.le
      _ = B * a := by rw [mul_assoc, mul_comm L x, hxL]
      _ ≤ _ := by nlinarith [haB]
  have hy₁ : 0 < y₁ := by dsimp [y₁, σ]; linarith
  have hy₂ : 0 < y₂ := by dsimp [y₂, σ]; linarith
  have h₁ : y₁ ≤ 9 * x / 8 := by dsimp [y₁, σ]; linarith
  have h₂ : y₂ ≤ 9 * x / 8 := by dsimp [y₂, σ]; linarith
  have hi : 1 / y₁ + 1 / y₂ ≤ 1 / x + D := by
    have he : σ - 1 = x := by dsimp [σ]; ring
    rw [he] at hup
    change 1 / y₁ + 1 / y₂ - 60000 * L ≤ _ at hpair
    dsimp [D]
    linarith
  exact two_real_zero_gaps_contradiction hx hy₁ hy₂ h₁ h₂ hDx hi
theorem exists_primitive_real_zero_box_subsingleton :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 →
      Set.Subsingleton {s : ℂ | 1 - c / Real.log ((q : ℝ) * 2) < s.re ∧
        |s.im| ≤ c / Real.log ((q : ℝ) * 2) ∧ DirichletCharacter.LFunction χ s = 0} := by
  obtain ⟨cR, hcR, hreal⟩ := exists_primitive_real_zero_box_im_eq_zero
  obtain ⟨cU, hcU, huniq⟩ := exists_primitive_real_zero_unique
  refine ⟨min cR cU, lt_min hcR hcU, ?_⟩
  intro q inst χ hq hχ hsq s hs t ht
  have hL : 0 < Real.log ((q : ℝ) * 2) := by
    have h := conductor_height_log_ge_threeQuarters q hq 0
    simp only [abs_zero, zero_add] at h
    linarith
  have hR := div_le_div_of_nonneg_right (min_le_left cR cU) hL.le
  have hU := div_le_div_of_nonneg_right (min_le_right cR cU) hL.le
  have hsi : s.im = 0 := hreal q χ hq hχ hsq s (by linarith [hs.1])
    (hs.2.1.trans hR) hs.2.2
  have hti : t.im = 0 := hreal q χ hq hχ hsq t (by linarith [ht.1])
    (ht.2.1.trans hR) ht.2.2
  have hsreal : (s.re : ℂ) = s := by apply Complex.ext <;> simp [hsi]
  have htreal : (t.re : ℂ) = t := by apply Complex.ext <;> simp [hti]
  have he := huniq q χ hq hχ hsq s.re t.re (by linarith [hs.1]) (by linarith [ht.1])
    (by rw [hsreal]; exact hs.2.2) (by rw [htreal]; exact ht.2.2)
  apply Complex.ext
  · exact he
  · rw [hsi, hti]
end Chen

end

/-! ## ChenTheorem.Lemma6.RealZeroSimplicity -/

section

namespace Chen
theorem exists_primitive_real_zero_deriv_ne_zero :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → ∀ β : ℝ,
      1 - c / Real.log ((q : ℝ) * 2) < β →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0 := by
  obtain ⟨δ, C, hδ, hC, hu⟩ := exists_real_character_logDeriv_real_axis_bound
  let B : ℝ := 2 * C + 60001
  have hB : 0 < B := by dsimp [B]; positivity
  let a : ℝ := min (δ / 4) (min (1 / 8) (1 / (4 * B)))
  have ha : 0 < a := by dsimp [a]; positivity
  have haδ : a ≤ δ / 4 := min_le_left _ _
  have ha8 : a ≤ 1 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have haB : a * B ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * B)).mp
      (show a ≤ 1 / (4 * B) from (min_le_right _ _).trans (min_le_right _ _))
    nlinarith
  refine ⟨a / 8, by positivity, ?_⟩
  intro q inst χ hq hχ hsq β hβ hf hdf
  let L : ℝ := Real.log ((q : ℝ) * 2)
  have hL : 3 / 4 ≤ L := by simpa [L] using conductor_height_log_ge_threeQuarters q hq 0
  have hLp : 0 < L := by linarith
  let x : ℝ := a / L
  let σ : ℝ := 1 + x
  let y : ℝ := σ - β
  let D : ℝ := C + Real.log q / 4 + 60000 * L
  have hx : 0 < x := div_pos ha hLp
  have hxL : x * L = a := div_mul_cancel₀ _ hLp.ne'
  have hxδ : x < δ := by apply (div_lt_iff₀ hLp).mpr; nlinarith
  have hx6 : x ≤ 1 / 6 := by apply (div_le_iff₀ hLp).mpr; linarith
  have hquot : (a / 8) / L = x / 8 := by dsimp [x]; ring
  change 1 - (a / 8) / L < β at hβ
  rw [hquot] at hβ
  have hb : β ≤ 1 := by
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; have := congrArg Complex.re he; simp at this; linarith))
      (by simpa using hh.le)) hf
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hσ' : σ ≤ 3 / 2 := by dsimp [σ]; linarith
  have hσδ : σ < 1 + δ := by dsimp [σ]; linarith
  have hmult := primitive_LFunction_logDeriv_re_ge_multiple_real_zero hq hχ σ β
    hσ hσ' (by linarith) hf hdf
  have hup := hu q χ hsq σ hσ hσδ
  have hlogq : Real.log q ≤ L := by
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < q))
    have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have hD : D ≤ B * L := by dsimp [D, B]; nlinarith
  have hDx : D * x ≤ 1 / 4 := by
    calc
      _ ≤ (B * L) * x := mul_le_mul_of_nonneg_right hD hx.le
      _ = B * a := by rw [mul_assoc, mul_comm L x, hxL]
      _ ≤ _ := by nlinarith [haB]
  have hy : 0 < y := by dsimp [y, σ]; linarith
  have hyx : y ≤ 9 * x / 8 := by dsimp [y, σ]; linarith
  have hi : 1 / y + 1 / y ≤ 1 / x + D := by
    have he : σ - 1 = x := by dsimp [σ]; ring
    rw [he] at hup
    change 2 / y - 60000 * L ≤ _ at hmult
    dsimp [D]
    rw [show (2 : ℝ) / y = 1 / y + 1 / y by ring] at hmult
    linarith
  exact two_real_zero_gaps_contradiction hx hy hy hyx hyx hDx hi
/-- A primitive real character has at most one zero in a uniform logarithmic
box about 1; any such zero is real and simple. No existence or Siegel bound is asserted. -/
theorem exists_primitive_real_zero_box_unique_real_simple :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 →
      (Set.Subsingleton {s : ℂ | 1 - c / Real.log ((q : ℝ) * 2) < s.re ∧
        |s.im| ≤ c / Real.log ((q : ℝ) * 2) ∧ DirichletCharacter.LFunction χ s = 0}) ∧
      ∀ s : ℂ, 1 - c / Real.log ((q : ℝ) * 2) < s.re →
        |s.im| ≤ c / Real.log ((q : ℝ) * 2) → DirichletCharacter.LFunction χ s = 0 →
        s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 := by
  obtain ⟨cU, hcU, hU⟩ := exists_primitive_real_zero_box_subsingleton
  obtain ⟨cR, hcR, hR⟩ := exists_primitive_real_zero_box_im_eq_zero
  obtain ⟨cS, hcS, hS⟩ := exists_primitive_real_zero_deriv_ne_zero
  let c := min cU (min cR cS)
  have hc : 0 < c := lt_min hcU (lt_min hcR hcS)
  refine ⟨c, hc, ?_⟩
  intro q inst χ hq hχ hsq
  have hL : 0 < Real.log ((q : ℝ) * 2) := by
    have h := conductor_height_log_ge_threeQuarters q hq 0
    simp only [abs_zero, zero_add] at h
    linarith
  have hcU' := div_le_div_of_nonneg_right (show c ≤ cU from min_le_left _ _) hL.le
  have hcR' := div_le_div_of_nonneg_right
    (show c ≤ cR from (min_le_right _ _).trans (min_le_left _ _)) hL.le
  have hcS' := div_le_div_of_nonneg_right
    (show c ≤ cS from (min_le_right _ _).trans (min_le_right _ _)) hL.le
  constructor
  · intro s hs t ht
    exact hU q χ hq hχ hsq
      ⟨by linarith [hs.1], hs.2.1.trans hcU', hs.2.2⟩
      ⟨by linarith [ht.1], ht.2.1.trans hcU', ht.2.2⟩
  · intro s hs ht hz
    have him := hR q χ hq hχ hsq s (by linarith) (ht.trans hcR') hz
    refine ⟨him, ?_⟩
    have he : (s.re : ℂ) = s := by apply Complex.ext <;> simp [him]
    have h := hS q χ hq hχ hsq s.re (by linarith) (by rw [he]; exact hz)
    simpa only [he] using h
end Chen

end

/-! ## ChenTheorem.Lemma6.RealLowHeightTools -/

section

namespace Chen
theorem conductor_height_log_le_twice_zero_height {q : ℕ} (hq : 2 ≤ q)
    (t : ℝ) (ht : |t| ≤ 1) :
    Real.log ((q : ℝ) * (|t| + 2)) ≤ 2 * Real.log ((q : ℝ) * 2) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  calc
    _ ≤ Real.log (((q : ℝ) * 2) ^ 2) := by
      apply Real.log_le_log (by positivity)
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ q by positivity) (sub_nonneg.mpr ht)]
    _ = _ := by rw [Real.log_pow]; norm_num
theorem principal_shifted_pole_re (x t : ℝ) :
    (((x : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)⁻¹).re =
      x / (x ^ 2 + 4 * t ^ 2) := by
  simp only [Complex.inv_re, Complex.normSq_apply, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.add_im, Complex.mul_im, mul_zero, sub_zero, add_zero, zero_add, mul_one]
  ring
theorem principal_shifted_pole_mul_le_one_fifth {x t : ℝ} (hx : 0 < x)
    (ht : x ≤ |t|) :
    (((x : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)⁻¹).re * x ≤ 1 / 5 := by
  rw [principal_shifted_pole_re, div_mul_eq_mul_div]
  have hden : 0 < x ^ 2 + 4 * t ^ 2 := by positivity
  apply (div_le_iff₀ hden).mpr
  have hsq := mul_self_le_mul_self hx.le ht
  rw [← sq, ← sq, sq_abs] at hsq
  nlinarith
theorem norm_principal_shifted_point_sub_one_le {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖(σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I - 1‖ ≤ σ - 1 + 2 * |t| := by
  have he : (σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I - 1 =
      ((σ - 1 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (by linarith : 0 < σ - 1)]
end Chen

end

/-! ## ChenTheorem.Lemma6.RealLowHeightRegion -/

section

namespace Chen

/-- For a fixed positive height, independent of the modulus, zeros of primitive
real characters sufficiently close to 1 must be real. -/
theorem exists_primitive_real_low_height_zero_im_eq_zero :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → ∀ s : ℂ,
        1 - c / Real.log ((q : ℝ) * 2) < s.re → |s.im| ≤ r →
        DirichletCharacter.LFunction χ s = 0 → s.im = 0 := by
  obtain ⟨c₀, hc₀, hbox⟩ := exists_primitive_real_zero_box_im_eq_zero
  obtain ⟨δz, Cz, hδz, hCz, hzeta⟩ := exists_zeta_real_logDeriv_pole_bound
  obtain ⟨δp, Cp, hδp, hCp, hprincipal⟩ := exists_principal_complex_logDeriv_pole_bound
  let B : ℝ := 4 * Cz + 2 * Cp + 480002
  have hB : 0 < B := by dsimp [B]; positivity
  let a : ℝ := min c₀ (min (δz / 4) (min (δp / 4) (min (1 / 8) (1 / (32 * B)))))
  have ha : 0 < a := by dsimp [a]; positivity
  have ha₀ : a ≤ c₀ := min_le_left _ _
  have haz : a ≤ δz / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hap : a ≤ δp / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have ha8 : a ≤ 1 / 8 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have haB : a * B ≤ 1 / 32 := by
    have h := (le_div_iff₀ (by positivity : 0 < 32 * B)).mp
      (show a ≤ 1 / (32 * B) from (min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    nlinarith
  let r : ℝ := min (δp / 8) 1
  have hr : 0 < r := lt_min (by positivity) zero_lt_one
  have hrp : r ≤ δp / 8 := min_le_left _ _
  have hr1 : r ≤ 1 := min_le_right _ _
  refine ⟨r, a / 8, hr, by positivity, ?_⟩
  intro q inst χ hq hχ hsq s hs ht hzero
  let L : ℝ := Real.log ((q : ℝ) * 2)
  have hL : 3 / 4 ≤ L := by simpa [L] using conductor_height_log_ge_threeQuarters q hq 0
  have hLp : 0 < L := by linarith
  have hcdiv : (a / 8) / L ≤ c₀ / L :=
    div_le_div_of_nonneg_right (by linarith) hLp.le
  change 1 - (a / 8) / L < s.re at hs
  by_cases htbox : |s.im| ≤ c₀ / L
  · exact hbox q χ hq hχ hsq s (by linarith) htbox hzero
  · exfalso
    let x : ℝ := a / L
    let σ : ℝ := 1 + x
    let y : ℝ := σ - s.re
    let P : ℝ := (((x : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I)⁻¹).re
    let E : ℝ := 3 * Cz + Cp + 240000 * Real.log ((q : ℝ) * (|s.im| + 2)) + Real.log q
    have hx : 0 < x := div_pos ha hLp
    have hxL : x * L = a := div_mul_cancel₀ _ hLp.ne'
    have hxt : x ≤ |s.im| := by
      have h := div_le_div_of_nonneg_right ha₀ hLp.le
      dsimp [x]
      linarith
    have hxz : x < δz := by apply (div_lt_iff₀ hLp).mpr; nlinarith
    have hxp : x < δp / 2 := by apply (div_lt_iff₀ hLp).mpr; nlinarith
    have hx6 : x ≤ 1 / 6 := by apply (div_le_iff₀ hLp).mpr; linarith
    have hquot : (a / 8) / L = x / 8 := by dsimp [x]; ring
    rw [hquot] at hs
    have hβ : s.re ≤ 1 := by
      by_contra! hh
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
        (Or.inr (by intro he; rw [he] at hh; norm_num at hh)) hh.le) hzero
    have hσ : 1 < σ := by dsimp [σ]; linarith
    have hσ' : σ ≤ 3 / 2 := by dsimp [σ]; linarith
    have hσz : σ < 1 + δz := by dsimp [σ]; linarith
    have hσp : ‖(σ : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I - 1‖ < δp := by
      apply (norm_principal_shifted_point_sub_one_le hσ s.im).trans_lt
      dsimp [σ]
      linarith
    have hπ : P * x ≤ 1 / 5 := principal_shifted_pole_mul_le_one_fifth hx hxt
    have hheight := conductor_height_log_le_twice_zero_height hq s.im (ht.trans hr1)
    have hlogq : Real.log q ≤ L := by
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < q))
      have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      linarith
    have hE : E ≤ B * L := by dsimp [E, B]; change _ ≤ 2 * L at hheight; nlinarith
    have hEx : E * x ≤ 1 / 32 := by
      calc
        _ ≤ (B * L) * x := mul_le_mul_of_nonneg_right hE hx.le
        _ = B * a := by rw [mul_assoc, mul_comm L x, hxL]
        _ ≤ _ := by nlinarith [haB]
    have hDx : (P + E) * x ≤ 1 / 4 := by nlinarith
    have hz : DirichletCharacter.LFunction χ ((s.re : ℂ) + (s.im : ℂ) * Complex.I) = 0 := by
      rw [Complex.re_add_im]; exact hzero
    have hi := primitive_real_zero_inequality hq hχ hsq σ s.re s.im Cz Cp
      hσ hσ' (by linarith) hz (hzeta σ hσ hσz)
      (hprincipal q _ (by simpa using hσ) hσp)
    have he : (σ : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I - 1 =
        (x : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I := by dsimp [σ]; push_cast; ring
    rw [he] at hi
    have hσx : σ - 1 = x := by dsimp [σ]; ring
    rw [hσx] at hi
    have hi' : 4 / y ≤ 3 / x + (P + E) := by dsimp [y, P, E]; linarith
    exact four_div_gap_contradiction hx (by dsimp [y]; linarith)
      (by dsimp [y, σ]; linarith) hDx hi'

/-- The fixed-height strip contains at most one zero, and it is real and simple. -/
theorem exists_primitive_real_low_height_unique_real_simple :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 →
        (Set.Subsingleton {s : ℂ | 1 - c / Real.log ((q : ℝ) * 2) < s.re ∧
          |s.im| ≤ r ∧ DirichletCharacter.LFunction χ s = 0}) ∧
        ∀ s : ℂ, 1 - c / Real.log ((q : ℝ) * 2) < s.re → |s.im| ≤ r →
          DirichletCharacter.LFunction χ s = 0 →
          s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 := by
  obtain ⟨r, cR, hr, hcR, hR⟩ := exists_primitive_real_low_height_zero_im_eq_zero
  obtain ⟨cU, hcU, hU⟩ := exists_primitive_real_zero_unique
  obtain ⟨cS, hcS, hS⟩ := exists_primitive_real_zero_deriv_ne_zero
  let c := min cR (min cU cS)
  have hc : 0 < c := lt_min hcR (lt_min hcU hcS)
  refine ⟨r, c, hr, hc, ?_⟩
  intro q inst χ hq hχ hsq
  have hL : 0 < Real.log ((q : ℝ) * 2) := by
    have h := conductor_height_log_ge_threeQuarters q hq 0
    simp only [abs_zero, zero_add] at h
    linarith
  have hcR' := div_le_div_of_nonneg_right (show c ≤ cR from min_le_left _ _) hL.le
  have hcU' := div_le_div_of_nonneg_right
    (show c ≤ cU from (min_le_right _ _).trans (min_le_left _ _)) hL.le
  have hcS' := div_le_div_of_nonneg_right
    (show c ≤ cS from (min_le_right _ _).trans (min_le_right _ _)) hL.le
  have hreal : ∀ s : ℂ, 1 - c / Real.log ((q : ℝ) * 2) < s.re → |s.im| ≤ r →
      DirichletCharacter.LFunction χ s = 0 → s.im = 0 := by
    intro s hs ht hz
    exact hR q χ hq hχ hsq s (by linarith) ht hz
  constructor
  · intro s hs t ht
    have hsi := hreal s hs.1 hs.2.1 hs.2.2
    have hti := hreal t ht.1 ht.2.1 ht.2.2
    have heS : (s.re : ℂ) = s := by apply Complex.ext <;> simp [hsi]
    have heT : (t.re : ℂ) = t := by apply Complex.ext <;> simp [hti]
    have he := hU q χ hq hχ hsq s.re t.re (by linarith [hs.1]) (by linarith [ht.1])
      (by rw [heS]; exact hs.2.2) (by rw [heT]; exact ht.2.2)
    apply Complex.ext
    · exact he
    · rw [hsi, hti]
  · intro s hs ht hz
    have him := hreal s hs ht hz
    refine ⟨him, ?_⟩
    have he : (s.re : ℂ) = s := by apply Complex.ext <;> simp [him]
    have h := hS q χ hq hχ hsq s.re (by linarith) (by rw [he]; exact hz)
    simpa only [he] using h

end Chen

end

/-! ## ChenTheorem.Lemma6.ZetaRightStripGrowth -/

section

open Set Metric

namespace Chen
theorem riemannZeta_eq_half_add_pole_add_integral (s : ℂ) (hs : 0 < s.re) (hsne : s ≠ 1) :
    riemannZeta s = (1 / 2 : ℂ) + 1 / (s - 1) +
      s * ∫ x in Ioi (1 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) := by
  have hs0 : s ≠ 0 := by intro he; rw [he] at hs; norm_num at hs
  rw [← Zeta0EqZeta (N := 1) (by norm_num) hs hsne]
  norm_num [riemannZeta0, Finset.sum_range_succ, Complex.zero_cpow, hs0]
  rw [show (1 : ℂ) - s = -(s - 1) by ring, div_neg]
  ring
theorem norm_riemannZeta_le_right_strip (s : ℂ) (hs : 0 < s.re) (hsne : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖s - 1‖ + ‖s‖ / s.re := by
  have hI := ZetaBnd_aux1b 1 (by norm_num) (σ := s.re) (t := s.im) hs
  rw [Complex.re_add_im] at hI
  norm_num only [Nat.cast_one, Real.one_rpow] at hI
  rw [riemannZeta_eq_half_add_pole_add_integral s hs hsne]
  apply (norm_add_le _ _).trans
  have hleft : ‖(1 / 2 : ℂ) + 1 / (s - 1)‖ ≤ 1 / 2 + 1 / ‖s - 1‖ := by
    simpa using norm_add_le (1 / 2 : ℂ) (1 / (s - 1))
  have hright : ‖s * ∫ x in Ioi (1 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      ‖s‖ / s.re := by
    rw [norm_mul]
    simpa only [one_div, div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hI (norm_nonneg s)
  linarith
theorem norm_riemannZeta_high_centered_disk_le (t : ℝ) (ht : 1 ≤ |t|)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖riemannZeta (dirichletZeroDiskCenter t + w)‖ ≤
      4 * (‖dirichletZeroDiskCenter t‖ + 1) := by
  let c := dirichletZeroDiskCenter t
  let s := c + w
  have hre : 3 / 4 ≤ s.re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm w).trans hw)).1
    dsimp [s, c]
    rw [dirichletZeroDiskCenter_re]
    linarith
  have hc : 1 ≤ ‖c - 1‖ := by
    have h := Complex.abs_im_le_norm (c - 1)
    have h' : |t| ≤ ‖c - 1‖ := by simpa [c, dirichletZeroDiskCenter] using h
    exact ht.trans h'
  have hden : 1 / 2 ≤ ‖s - 1‖ := by
    have h := norm_sub_le (s - 1) w
    have he : s - 1 - w = c - 1 := by dsimp [s]; ring
    rw [he] at h
    linarith
  have hsne : s ≠ 1 := by intro he; rw [he, sub_self, norm_zero] at hden; norm_num at hden
  have hb := norm_riemannZeta_le_right_strip s (by linarith) hsne
  have hnorm : ‖s‖ ≤ ‖c‖ + 1 / 2 := (norm_add_le _ _).trans (by linarith)
  have hinv : 1 / ‖s - 1‖ ≤ 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden
    norm_num at h
    simpa only [one_div] using h
  have hquot : ‖s‖ / s.re ≤ 2 * ‖s‖ := by
    apply (div_le_iff₀ (by linarith : 0 < s.re)).mpr
    nlinarith [norm_nonneg s]
  change ‖riemannZeta s‖ ≤ 4 * (‖c‖ + 1)
  linarith [norm_nonneg c]
end Chen

end

/-! ## ChenTheorem.Lemma6.ZetaCircleGrowth -/

section

namespace Chen
theorem siegel_circle_geometry {s : ℂ} (hs : s ∈ Metric.sphere (2 : ℂ) (3 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ s.re ∧ ‖s‖ ≤ 7 / 2 ∧ (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
  have hnorm : ‖s - 2‖ = (3 / 2 : ℝ) := by simpa only [Metric.mem_sphere, dist_eq_norm] using hs
  have hre := (Complex.abs_re_le_norm (s - 2))
  have hnorms := norm_add_le (s - 2) (2 : ℂ)
  have hpole := norm_sub_le (s - 1) (1 : ℂ)
  norm_num only [Complex.sub_re, Complex.re_ofNat, hnorm, Complex.norm_ofNat,
    norm_one, sub_add_cancel] at hre hnorms hpole
  rw [show s - 1 - 1 = s - 2 by ring, hnorm] at hpole
  norm_num at hpole
  exact ⟨by linarith [(abs_le.mp hre).1], by linarith, by linarith⟩
theorem norm_riemannZeta_siegel_circle_le {s : ℂ}
    (hs : s ∈ Metric.sphere (2 : ℂ) (3 / 2 : ℝ)) : ‖riemannZeta s‖ ≤ 10 := by
  obtain ⟨hre, hnorm, hpole⟩ := siegel_circle_geometry hs
  have hsne : s ≠ 1 := by intro h; norm_num [h] at hpole
  have hb := norm_riemannZeta_le_right_strip (s := s) (by linarith) hsne
  have h1 : 1 / ‖s - 1‖ ≤ (2 : ℝ) := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have h2 : ‖s‖ / s.re ≤ (7 : ℝ) := (div_le_iff₀ (by linarith)).mpr (by linarith)
  linarith

end Chen

end

/-! ## ChenTheorem.Lemma6.BiquadraticTaylor -/

section

namespace Chen

theorem zeta_mul_biquadraticHolomorphicFactor {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (s : ℂ) :
    riemannZeta s * biquadraticHolomorphicFactor χ ψ s = biquadraticLFunction χ ψ s := by
  unfold biquadraticHolomorphicFactor biquadraticLFunction
  ring

theorem backwardTaylorCoeff_biquadraticRegularPart {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) (n : ℕ) :
    backwardTaylorCoeff (biquadraticRegularPart χ ψ) 2 n =
      backwardTaylorCoeff (biquadraticLFunction χ ψ) 2 n - biquadraticResidue χ ψ := by
  have h := backwardTaylorCoeff_regularizedZetaMul
    (differentiable_biquadraticHolomorphicFactor χ ψ hχ hψ hχψ) n
  simpa only [zeta_mul_biquadraticHolomorphicFactor, biquadraticRegularPart, biquadraticResidue] using h

theorem hasSum_biquadraticRegularPart_backwardTaylor {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) (z : ℂ) :
    HasSum (fun n : ℕ => (backwardTaylorCoeff (biquadraticLFunction χ ψ) 2 n -
      biquadraticResidue χ ψ) * z ^ n) (biquadraticRegularPart χ ψ (2 - z)) := by
  have h := hasSum_regularizedZetaMul_backwardTaylor
    (differentiable_biquadraticHolomorphicFactor χ ψ hχ hψ hχψ) z
  simpa only [zeta_mul_biquadraticHolomorphicFactor, biquadraticRegularPart, biquadraticResidue] using h

theorem norm_biquadraticRegularPart_circle_le {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) {B : ℝ} (hB : 0 ≤ B) {s : ℂ}
    (hs : s ∈ Metric.sphere (2 : ℂ) (3 / 2 : ℝ))
    (hf : ‖biquadraticHolomorphicFactor χ ψ s‖ ≤ B) (hr : ‖biquadraticResidue χ ψ‖ ≤ B) :
    ‖biquadraticRegularPart χ ψ s‖ ≤ 12 * B := by
  have hpole := (siegel_circle_geometry hs).2.2
  have hsne : s ≠ 1 := by intro h; norm_num [h] at hpole
  have hprod : ‖biquadraticLFunction χ ψ s‖ ≤ 10 * B := by
    rw [← zeta_mul_biquadraticHolomorphicFactor, norm_mul]
    exact mul_le_mul (norm_riemannZeta_siegel_circle_le hs) hf (norm_nonneg _) (by norm_num)
  have hres : ‖biquadraticResidue χ ψ / (s - 1)‖ ≤ 2 * B := by
    rw [norm_div]
    apply (div_le_iff₀ (by linarith : 0 < ‖s - 1‖)).mpr
    have := mul_le_mul_of_nonneg_left hpole (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB)
    linarith
  rw [biquadraticRegularPart_eq χ ψ hsne]
  exact (norm_sub_le _ _).trans (by linarith)

theorem norm_biquadraticTaylor_sub_residue_le {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2 : ℝ), ‖biquadraticHolomorphicFactor χ ψ s‖ ≤ B)
    (hr : ‖biquadraticResidue χ ψ‖ ≤ B) (n : ℕ) :
    ‖backwardTaylorCoeff (biquadraticLFunction χ ψ) 2 n - biquadraticResidue χ ψ‖ ≤
      (12 * B) * (2 / 3 : ℝ) ^ n := by
  rw [← backwardTaylorCoeff_biquadraticRegularPart χ ψ hχ hψ hχψ]
  have h := norm_backwardTaylorCoeff_le (R := (3 / 2 : ℝ)) (M := 12 * B) (by norm_num)
    (differentiable_biquadraticRegularPart χ ψ hχ hψ hχψ).diffContOnCl
    (fun s hs => norm_biquadraticRegularPart_circle_le χ ψ hB hs (hf s hs) hr) n
  norm_num only [show (3 / 2 : ℝ)⁻¹ = 2 / 3 by norm_num] at h
  exact h

end Chen

end

/-! ## ChenTheorem.Lemma6.BiquadraticTaylorBound -/

section

namespace Chen

theorem norm_biquadraticHolomorphicFactor_compact_le {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1)
    {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) (hnorm : ‖s‖ ≤ 7 / 2) :
    ‖biquadraticHolomorphicFactor χ ψ s‖ ≤ (42 * (q : ℝ) ^ 3) ^ 3 := by
  have h1 := norm_nonprincipal_LFunction_compact_le χ hχ hs hnorm
  have h2 := norm_nonprincipal_LFunction_compact_le ψ hψ hs hnorm
  have h3 := norm_nonprincipal_LFunction_compact_le (χ * ψ) hχψ hs hnorm
  simp only [biquadraticHolomorphicFactor, norm_mul]
  calc
    _ ≤ (42 * (q : ℝ) ^ 3) * (42 * (q : ℝ) ^ 3) * (42 * (q : ℝ) ^ 3) :=
      mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem norm_biquadraticResidue_le {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    ‖biquadraticResidue χ ψ‖ ≤ (42 * (q : ℝ) ^ 3) ^ 3 :=
  norm_biquadraticHolomorphicFactor_compact_le χ ψ hχ hψ hχψ (s := 1) (by norm_num) (by norm_num)

/-- The actual Taylor coefficients satisfy a uniform conductor-polynomial bound;
no growth assumptions remain in this statement. -/
theorem norm_biquadraticTaylor_sub_residue_le_level {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) (n : ℕ) :
    ‖backwardTaylorCoeff (biquadraticLFunction χ ψ) 2 n - biquadraticResidue χ ψ‖ ≤
      (12 * (42 * (q : ℝ) ^ 3) ^ 3) * (2 / 3 : ℝ) ^ n := by
  apply norm_biquadraticTaylor_sub_residue_le χ ψ hχ hψ hχψ (by positivity)
  · intro s hs
    obtain ⟨hre, hnorm, _⟩ := siegel_circle_geometry hs
    exact norm_biquadraticHolomorphicFactor_compact_le χ ψ hχ hψ hχψ hre hnorm
  · exact norm_biquadraticResidue_le χ ψ hχ hψ hχψ

end Chen

end

/-! ## ChenTheorem.Lemma6.BiquadraticTaylorLower -/

section

open ComplexConjugate

namespace Chen

theorem biquadraticResidue_eq_re {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1)
    (hχsq : χ ^ 2 = 1) (hψsq : ψ ^ 2 = 1) :
    ((biquadraticResidue χ ψ).re : ℂ) = biquadraticResidue χ ψ := by
  apply Complex.conj_eq_iff_re.mp
  have hprodsq : (χ * ψ) ^ 2 = 1 := by rw [mul_pow, hχsq, hψsq, one_mul]
  simp only [biquadraticResidue, biquadraticHolomorphicFactor, map_mul,
    conj_LFunction_of_nonprincipal_real_character χ hχ hχsq,
    conj_LFunction_of_nonprincipal_real_character ψ hψ hψsq,
    conj_LFunction_of_nonprincipal_real_character (χ * ψ) hχψ hprodsq, map_one]

/-- The quantitative finite Taylor inequality for the actual biquadratic product.
It holds before any truncation index is chosen. -/
theorem biquadraticLFunction_taylor_lower_bound {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1)
    (hχsq : χ ^ 2 = 1) (hψsq : ψ ^ 2 = 1) (β : ℝ)
    (hβ : 7 / 8 < β) (hβ' : β < 1) (k : ℕ) (hk : 1 ≤ k) :
    1 - (biquadraticResidue χ ψ).re * (2 - β) ^ k / (1 - β) -
      (12 * (42 * (q : ℝ) ^ 3) ^ 3) * ((2 / 3 : ℝ) * (2 - β)) ^ k /
        (1 - (2 / 3 : ℝ) * (2 - β)) ≤ (biquadraticLFunction χ ψ (β : ℂ)).re := by
  have hρ := biquadraticResidue_eq_re χ ψ hχ hψ hχψ hχsq hψsq
  have hb (n : ℕ) : 0 ≤ (backwardTaylorCoeff (biquadraticLFunction χ ψ) 2 n).re :=
    (Complex.le_def.mp (backwardTaylorCoeff_biquadratic_nonneg χ ψ hχsq hψsq 2 (by norm_num) n)).1
  have hb0 : 1 ≤ (backwardTaylorCoeff (biquadraticLFunction χ ψ) 2 0).re := by
    simpa [backwardTaylorCoeff] using
      (Complex.le_def.mp (biquadraticLFunction_real_ge_one χ ψ hχsq hψsq 2 (by norm_num))).1
  have hbound (n : ℕ) := norm_biquadraticTaylor_sub_residue_le_level χ ψ hχ hψ hχψ n
  have hsum := hasSum_biquadraticRegularPart_backwardTaylor χ ψ hχ hψ hχψ ((2 - β : ℝ) : ℂ)
  have heval : (2 : ℂ) - ((2 - β : ℝ) : ℂ) = (β : ℂ) := by push_cast; ring
  rw [heval, biquadraticRegularPart_eq χ ψ (by exact_mod_cast ne_of_lt hβ')] at hsum
  have hvalue : biquadraticLFunction χ ψ (β : ℂ) - biquadraticResidue χ ψ / ((β : ℂ) - 1) =
      biquadraticLFunction χ ψ (β : ℂ) + (((biquadraticResidue χ ψ).re / ((2 - β) - 1) : ℝ) : ℂ) := by
    rw [← hρ]
    simp only [Complex.ofReal_re]
    push_cast
    have he : (2 : ℂ) - β - 1 = -((β : ℂ) - 1) := by ring
    rw [he, div_neg]
    ring
  rw [hvalue, ← hρ] at hsum
  have h := siegelTaylor_lower_bound hb hb0 (by linarith : (1 : ℝ) < 2 - β)
    (by norm_num : (0 : ℝ) ≤ 2 / 3) (by linarith : (2 / 3 : ℝ) * (2 - β) < 1)
    (fun n => by rw [hρ]; exact hbound n) hsum k hk
  simpa only [show (2 - β) - 1 = 1 - β by ring] using h

end Chen

end

