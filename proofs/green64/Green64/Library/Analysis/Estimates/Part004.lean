module

public import Green64.Library.Analysis.Estimates.SourcePrimeFactorialMoment
public import Green64.Library.Analysis.Estimates.Part002
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Green64.Library.Analysis.Estimates.Part001
public import Green64.Library.Sieve.Foundations.Part002
public import Mathlib
public import Green64.Library.Weights.Part006
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Green64.Library.Weights.Part002
public import Green64.Library.Weights.Part001
public import Mathlib.Tactic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Green64.Library.Correlation.Part001

@[expose] public section

/-!
# Analysis / Estimates / Part004

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceShortPrimeNormBudget -/

section

/-! Quantitative dyadic normalization of the exact growing-prime factorial moment.
The prime coefficients remain genuine `b_s(p) / p`; no prime-counting
asymptotics or divisor moments of growing order are assumed. -/

namespace Green64Analytic.CorrelationMellin

theorem source_short_prime_square_budget
    (s : Finset ℕ) (P : ℕ) (C : ℝ) (w : ℕ → ℂ)
    (hP : 1 ≤ P) (hC : 0 ≤ C)
    (hSupp : s ⊆ Finset.Icc P (2*P))
    (hW : ∀ p ∈ s, ‖w p‖ ≤ C/(P:ℝ)) :
    (∑ p ∈ s, ‖w p‖ ^ 2) ≤ 2*C^2/(P:ℝ) := by
  classical
  have hpp : (0:ℝ) < P := by exact_mod_cast (Nat.zero_lt_of_lt hP)
  have hcard : (s.card : ℝ) ≤ 2*(P:ℝ) := by
    have hs : s.card ≤ (Finset.Icc P (2*P)).card := Finset.card_le_card hSupp
    have hinterval : (Finset.Icc P (2*P)).card = P + 1 := by
      rw [Nat.card_Icc]
      omega
    rw [hinterval] at hs
    have h1 : P+1 ≤ 2*P := by omega
    exact_mod_cast hs.trans h1
  calc
    _ ≤ ∑ p ∈ s, (C/(P:ℝ))^2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg hC hpp.le)).mpr (hW p hp)
    _ = (s.card : ℝ) * (C/(P:ℝ))^2 := by simp
    _ ≤ (2*(P:ℝ)) * (C/(P:ℝ))^2 := by
      exact mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = 2*C^2/(P:ℝ) := by field_simp <;> ring

/-- Real normalized source marked-prime Dirichlet coefficients: the
square-mass budget follows from `‖b_s(p)‖ ≤ C`, with the true `1/p`.
No prime-number theorem is used in this dyadic counting bound. -/
theorem source_short_prime_reciprocal_square_budget
    (s : Finset ℕ) (P : ℕ) (C : ℝ) (b : ℕ → ℂ)
    (hP : 1 ≤ P) (hC : 0 ≤ C)
    (hSupp : s ⊆ Finset.Icc P (2*P))
    (hB : ∀ p ∈ s, ‖b p‖ ≤ C) :
    (∑ p ∈ s, ‖b p * ((p:ℂ)⁻¹)‖ ^ 2) ≤ 2*C^2/(P:ℝ) := by
  classical
  apply source_short_prime_square_budget s P C
    (fun p => b p * ((p:ℂ)⁻¹)) hP hC hSupp
  intro p hp
  have hpN : P ≤ p := (Finset.mem_Icc.mp (hSupp hp)).1
  have hpReal : (0:ℝ) < p := by exact_mod_cast lt_of_lt_of_le hP hpN
  have hPReal : (0:ℝ) < P := by exact_mod_cast (Nat.zero_lt_of_lt hP)
  have hPp : (P:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpN
  calc
    ‖b p * ((p:ℂ)⁻¹)‖ = ‖b p‖ / (p:ℝ) := by
      simp only [norm_mul, norm_inv, norm_natCast]
      ring
    _ ≤ C / (p:ℝ) := div_le_div_of_nonneg_right (hB p hp) hpReal.le
    _ ≤ C / (P:ℝ) := by
      apply (div_le_div_iff₀ hpReal hPReal).mpr
      exact mul_le_mul_of_nonneg_left hPp hC
end Green64Analytic.CorrelationMellin

end

/-! ## SourceExceptionalMomentCount -/

section

/-!
Finite quantitative threshold step in source sh:exceptional-count.
The analytic separated-time second-moment theorem is a separate input.
-/

namespace Green64Analytic.CorrelationMellin

theorem source_exceptional_threshold_count
    {ι : Type*} (J : Finset ι) (P : ι → ℂ)
    (j : ℕ) (δ E : ℝ) (hδ : 0 ≤ δ)
    (hlower : ∀ i ∈ J, δ ≤ ‖P i‖)
    (hmoment : (∑ i ∈ J, ‖(P i)^j‖ ^ 2) ≤ E) :
    (J.card : ℝ) * δ ^ (2*j) ≤ E := by
  classical
  calc
    _ = ∑ i ∈ J, δ ^ (2*j) := by simp
    _ ≤ ∑ i ∈ J, ‖(P i)^j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        δ ^ (2*j) = (δ ^ j) ^ 2 := by ring
        _ ≤ (‖P i‖ ^ j) ^ 2 := by
          gcongr
          exact hlower i hi
        _ = ‖(P i)^j‖ ^ 2 := by rw [norm_pow]
    _ ≤ E := hmoment
end Green64Analytic.CorrelationMellin

end

/-! ## SourceExceptionalFullMoment -/

section

/-! Exact assembly of the growing-order short-prime exceptional-time
moment.  Only the genuinely analytic separated-frequency evaluation
estimate is left as an explicit input. -/

namespace Green64Analytic.CorrelationMellin

noncomputable def sourcePrimePowerSupport (s : Finset ℕ) (j : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})).image
    (fun f => (primeTupleList s j f).prod)

noncomputable def sourcePrimePowerCoefficients (s : Finset ℕ) (j : ℕ)
    (w : {p : ℕ // p ∈ s} → ℂ) (n : ℕ) : ℂ :=
  ∑ f ∈ (Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})).filter
    (fun f => (primeTupleList s j f).prod = n), ∏ i, w (f i)

theorem source_prime_power_exact (s : Finset ℕ) (j : ℕ)
    (hprime : ∀ p ∈ s, Nat.Prime p)
    (w : {p : ℕ // p ∈ s} → ℂ) (t : ℝ) :
    (∑ p : {p : ℕ // p ∈ s}, w p * sourcePhase p.val t)^j =
      ∑ n ∈ sourcePrimePowerSupport s j,
        sourcePrimePowerCoefficients s j w n * sourcePhase n t := by
  simpa only [sourcePrimePowerSupport, sourcePrimePowerCoefficients] using
    source_short_prime_power_collapsed s j hprime w t

theorem source_prime_power_exact_sqnorm (s : Finset ℕ) (j : ℕ)
    (hprime : ∀ p ∈ s, Nat.Prime p)
    (w : {p : ℕ // p ∈ s} → ℂ) :
    (∑ n ∈ sourcePrimePowerSupport s j,
      ‖sourcePrimePowerCoefficients s j w n‖ ^ 2) ≤
      (j.factorial : ℝ) * (∑ p : {p : ℕ // p ∈ s}, ‖w p‖ ^ 2) ^ j := by
  simpa only [sourcePrimePowerSupport, sourcePrimePowerCoefficients] using
    source_short_prime_factorial_moment s j hprime w

/-- No fixed-order divisor moment: this remains true for `j0` growing
with `L`.  The sole analytic hypothesis is an L² bound for the exact
collapsed power on the actual selected exceptional frequencies. -/
theorem source_exceptional_count_of_power_evaluation
    {ι : Type*} (J : Finset ι) (times : ι → ℝ)
    (s : Finset ℕ) (j : ℕ) (hprime : ∀ p ∈ s, Nat.Prime p)
    (w : {p : ℕ // p ∈ s} → ℂ)
    (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hlarge : ∀ i ∈ J,
      δ ≤ ‖∑ p : {p : ℕ // p ∈ s}, w p * sourcePhase p.val (times i)‖)
    (hsparse :
      (∑ i ∈ J,
        ‖∑ n ∈ sourcePrimePowerSupport s j,
          sourcePrimePowerCoefficients s j w n * sourcePhase n (times i)‖ ^ 2) ≤
        B * ∑ n ∈ sourcePrimePowerSupport s j,
          ‖sourcePrimePowerCoefficients s j w n‖ ^ 2) :
    (J.card : ℝ) * δ ^ (2*j) ≤
       B * ((j.factorial : ℝ) *
         (∑ p : {p : ℕ // p ∈ s}, ‖w p‖ ^ 2) ^ j) := by
  classical
  let P : ι → ℂ := fun i =>
    ∑ p : {p : ℕ // p ∈ s}, w p * sourcePhase p.val (times i)
  have hpower (i : ι) :
      (P i)^j = ∑ n ∈ sourcePrimePowerSupport s j,
        sourcePrimePowerCoefficients s j w n * sourcePhase n (times i) :=
    source_prime_power_exact s j hprime w (times i)
  have hmoment :
      (∑ i ∈ J, ‖(P i)^j‖ ^ 2) ≤
        B * ((j.factorial : ℝ) *
          (∑ p : {p : ℕ // p ∈ s}, ‖w p‖ ^ 2) ^ j) := by
    calc
      _ = ∑ i ∈ J, ‖∑ n ∈ sourcePrimePowerSupport s j,
          sourcePrimePowerCoefficients s j w n * sourcePhase n (times i)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hpower]
      _ ≤ B * ∑ n ∈ sourcePrimePowerSupport s j,
          ‖sourcePrimePowerCoefficients s j w n‖ ^ 2 := hsparse
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (source_prime_power_exact_sqnorm s j hprime w) hB
  exact source_exceptional_threshold_count J P j δ _ hδ
    (fun i hi => hlarge i hi) hmoment
end Green64Analytic.CorrelationMellin

end

/-! ## SourcePrimePowerSupportBudget -/

section

/-!
Genuine support bound for the growing power of the short-prime source
polynomial.  This is the elementary but necessary `j0`/`Y` scale step.
-/

namespace Green64Analytic.CorrelationMellin

theorem source_prime_power_support_within_Y
    (s : Finset ℕ) (j P Y : ℕ)
    (hP : 1 ≤ P)
    (hS : s ⊆ Finset.Icc P (2*P))
    (hY : (2*P)^j ≤ Y) :
    sourcePrimePowerSupport s j ⊆ Finset.Icc 1 Y := by
  classical
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨f, _, rfl⟩
  have hlow (i : Fin j) : 1 ≤ (f i).val := by
    have hp := (Finset.mem_Icc.mp (hS (f i).property)).1
    omega
  have hupp (i : Fin j) : (f i).val ≤ 2*P :=
    (Finset.mem_Icc.mp (hS (f i).property)).2
  have lower : 1 ≤ (∏ i : Fin j, (f i).val) := by
    calc
      1 = ∏ _i : Fin j, (1:ℕ) := by simp
      _ ≤ ∏ i : Fin j, (f i).val := by
        exact Finset.prod_le_prod (fun i hi => hlow i)
  have upper : (∏ i : Fin j, (f i).val) ≤ Y := by
    calc
      _ ≤ ∏ _i : Fin j, (2*P) := by
        exact Finset.prod_le_prod (fun i hi => hupp i)
      _ = (2*P)^j := by simp
      _ ≤ Y := hY
  simp only [sourcePrimePowerSupport, primeTupleList] at hn ⊢
  rw [List.prod_ofFn]
  exact Finset.mem_Icc.mpr ⟨lower, upper⟩
end Green64Analytic.CorrelationMellin

end

/-! ## SourcePrimeLogOrder -/

section

/-! The source exceptional-moment order is the exact floor of the
base-(2P) real logarithm, with kernel-checked upper/lower power bounds. -/

namespace Green64Analytic.CorrelationMellin

def sourcePrimeMomentOrder (P Y : ℕ) : ℕ := Nat.log (2*P) Y

theorem source_prime_moment_order_power_bounds (P Y : ℕ)
    (hP : 1 ≤ P) (hY : 1 ≤ Y) :
    (2*P)^(sourcePrimeMomentOrder P Y) ≤ Y ∧
      Y < (2*P)^(sourcePrimeMomentOrder P Y + 1) := by
  have hbase : 1 < 2*P := by omega
  constructor
  · exact Nat.pow_log_le_self (2*P) (Nat.ne_of_gt hY)
  · exact Nat.lt_pow_succ_log_self hbase Y

theorem source_prime_moment_order_eq_natFloor (P Y : ℕ) :
    sourcePrimeMomentOrder P Y =
      ⌊Real.log (Y:ℝ) / Real.log (2*P:ℝ)⌋₊ := by
  simpa only [sourcePrimeMomentOrder, Real.logb, Nat.cast_mul, Nat.cast_ofNat] using
    (Real.natFloor_logb_natCast (2*P) Y).symm
end Green64Analytic.CorrelationMellin

end

/-! ## SourceFloorArcGeometry -/

section

namespace Green64Analytic.CorrelationD

/-- For H'≥2R, the exact floor Dirichlet cut-off
Q=⌊H'/R⌋ lies between H'/(2R) and H'/R.
This is the precise source major-arc radius comparison. -/
theorem source_floor_dirichlet_two_sided
    (Hprime R : ℝ) (hR : 0 < R) (hHR : 2*R ≤ Hprime) :
    0 < (⌊Hprime/R⌋₊ : ℕ) ∧
      Hprime/(2*R) ≤ (⌊Hprime/R⌋₊ : ℝ) ∧
      (⌊Hprime/R⌋₊ : ℝ) ≤ Hprime/R := by
  have hHp : 0 < Hprime := by linarith
  have hd : (2:ℝ) ≤ Hprime/R := by
    apply (le_div_iff₀ hR).mpr
    nlinarith [hHR]
  let Q : ℕ := ⌊Hprime/R⌋₊
  have hQpos : 0 < Q := by
    exact Nat.floor_pos.mpr (by linarith : (1:ℝ) ≤ Hprime/R)
  have hUp : (Q:ℝ) ≤ Hprime/R :=
    Nat.floor_le (by positivity)
  have hFloor : Hprime/R < (Q:ℝ)+1 :=
    Nat.lt_floor_add_one (Hprime/R)
  have hdiv : Hprime/(2*R) = (Hprime/R)/2 := by
    field_simp
  have hLo : Hprime/(2*R) ≤ (Q:ℝ) := by
    rw [hdiv]
    linarith
  exact ⟨hQpos,hLo,hUp⟩

theorem source_floor_reciprocal_radius
    (Hprime R : ℝ) (hR : 0 < R) (hHR : 2*R ≤ Hprime) :
    1/((⌊Hprime/R⌋₊ : ℝ)) ≤ (2*R)/Hprime := by
  obtain ⟨hQ,hQlo,hQhi⟩ :=
    source_floor_dirichlet_two_sided Hprime R hR hHR
  have hHp : 0 < Hprime := by linarith
  have hdiv : 0 < Hprime/(2*R) := by positivity
  calc
    1/((⌊Hprime/R⌋₊:ℝ)) ≤ 1/(Hprime/(2*R)) :=
      one_div_le_one_div_of_le hdiv hQlo
    _ = (2*R)/Hprime := by field_simp
end Green64Analytic.CorrelationD

end

/-! ## SourceDirichletArcRadius -/

section

namespace Green64Analytic.CorrelationD

/-- For the real signed nonzero source k and every Dirichlet
denominator r≥1, the signed lift has radius at most 2R/H'.
Neither an irrational frequency nor an unproved major-arc
assumption is needed. -/
theorem source_dirichlet_lift_radius
    (k : ℤ) (r : ℕ) (Hprime R : ℝ)
    (hk : k ≠ 0) (hr : 0 < r)
    (hR : 0 < R) (hHR : 2*R ≤ Hprime) :
    (1/(((⌊Hprime/R⌋₊:ℝ)+1)*(r:ℝ))) /
       |(k:ℝ)| ≤ (2*R)/Hprime := by
  have hrge : (1:ℝ) ≤ (r:ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hr))
  have hknat : 1 ≤ k.natAbs :=
    Nat.one_le_iff_ne_zero.mpr ((Int.natAbs_ne_zero).mpr hk)
  have hkabs : (1:ℝ) ≤ |(k:ℝ)| := by
    have hkn : (1:ℝ) ≤ (k.natAbs:ℝ) := by
      exact_mod_cast hknat
    have hh : ((k.natAbs:ℕ):ℝ) = |(k:ℝ)| := by
      have hi := congrArg (fun x : ℤ => (x : ℝ))
        (Int.natCast_natAbs k)
      simpa only [Int.cast_natCast, Int.cast_abs] using hi
    rwa [hh] at hkn
  obtain ⟨hQ,hQlo,hQhi⟩ :=
    source_floor_dirichlet_two_sided Hprime R hR hHR
  have hQr : (0:ℝ) < (⌊Hprime/R⌋₊:ℝ) :=
    Nat.cast_pos.mpr hQ
  have hden : (⌊Hprime/R⌋₊:ℝ) ≤
      ((⌊Hprime/R⌋₊:ℝ)+1)*(r:ℝ) := by
    have hQr1 : (1:ℝ) ≤ (⌊Hprime/R⌋₊:ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hQ))
    nlinarith
  have hInner : 1/(((⌊Hprime/R⌋₊:ℝ)+1)*(r:ℝ)) ≤
      1/(⌊Hprime/R⌋₊:ℝ) :=
    one_div_le_one_div_of_le hQr hden
  calc
    (1/(((⌊Hprime/R⌋₊:ℝ)+1)*(r:ℝ))) / |(k:ℝ)| ≤
      1/(((⌊Hprime/R⌋₊:ℝ)+1)*(r:ℝ)) :=
        div_le_self (by positivity) hkabs
    _ ≤ 1/(⌊Hprime/R⌋₊:ℝ) := hInner
    _ ≤ 2*R/Hprime :=
      source_floor_reciprocal_radius Hprime R hR hHR
end Green64Analytic.CorrelationD

end

/-! ## SourceCircleDirichletArc -/

section

namespace Green64Analytic.CorrelationD

/-- Complete quantitative circle lift of Dirichlet's approximation
for the original signed integer factor k. We retain its original
reduced a/r, exact Q=floor(H'/R), integer translate modulo 1,
and the honest q=|k|r denominator of the lifted rational center.
The center h0/q need not itself be reduced; that is harmless for
a major-arc covering by all reduced/nonreduced centers. -/
theorem source_circle_dirichlet_lift
    (k : ℤ) (theta Hprime R : ℝ)
    (hk : k ≠ 0) (hR : 0 < R)
    (hHR : 2*R ≤ Hprime) :
    ∃ (a : ℤ) (r q : ℕ) (h0 z : ℤ),
      0 < r ∧ r ≤ ⌊Hprime/R⌋₊ ∧
      Int.gcd a (r:ℤ) = 1 ∧
      |(k:ℝ)*theta-(a:ℝ)/(r:ℝ)| ≤ 1/((r:ℝ)^2) ∧
      q = k.natAbs*r ∧ 0 < q ∧
      q ≤ k.natAbs*⌊Hprime/R⌋₊ ∧
      0 ≤ h0 ∧ h0 < (q:ℤ) ∧
      |theta-(z:ℝ)-(h0:ℝ)/(q:ℝ)| ≤ 2*R/Hprime := by
  have hH : R ≤ Hprime := by linarith
  obtain ⟨hQ, a, r, hr, hrCap, hrReal, hcop, hDir, hC6⟩ :=
    source_dirichlet_floor_Hprime k theta Hprime R hR hH
  let Q : ℕ := ⌊Hprime/R⌋₊
  let delta : ℝ := 1/(((Q:ℝ)+1)*(r:ℝ))
  have hnear : |(k:ℝ)*theta - (a:ℝ)/(r:ℝ) - ((0:ℤ):ℝ)| ≤ delta := by
    simpa only [Int.cast_zero, sub_zero, delta, Q] using hDir
  obtain ⟨h0, q, z, hq, hqpos, hh0, hh0lt, hArc⟩ :=
    Green64CorrArc.lift_circle_rational_center
      k a 0 r theta delta hk hr hnear
  have hqmax : q ≤ k.natAbs*⌊Hprime/R⌋₊ := by
    rw [hq]
    exact Nat.mul_le_mul_left k.natAbs hrCap
  have hrad : delta/|(k:ℝ)| ≤ 2*R/Hprime :=
    source_dirichlet_lift_radius k r Hprime R hk hr hR hHR
  exact ⟨a, r, q, h0, z,
    hr, hrCap, hcop, hC6, hq, hqpos, hqmax, hh0, hh0lt,
    hArc.trans hrad⟩
end Green64Analytic.CorrelationD

end

/-! ## SourceFourTermScale -/

section

namespace Green64SourceC6

/-- Quantitative transfer of the exact C6 bracket from containing
dyadic cells P≤M, Q≤N to the four source minor-arc terms.
The inequality hbound is supplied by the already proven C6 theorem;
this numeric theorem imposes no new assumption on the coefficients. -/
theorem normalized_c6_four_term_sq
    (s A B P Q M N r : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q)
    (hM : 0 < M) (hN : 0 < N) (hr : 1 ≤ r)
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hs : 0 ≤ s)
    (hbound : s ≤
      5 * Real.sqrt (A/M) * Real.sqrt (B/N) *
        Real.sqrt (P + (1+Q/r)*(P+r*Real.log (2*r)))) :
    s^2 ≤ 50*A*B*(1/N+1/r+Real.log (2*r)/M+
      r*Real.log (2*r)/(M*N)) := by
  have hrpos : 0 < r := by linarith
  have hlog : 0 ≤ Real.log (2*r) := Real.log_nonneg (by nlinarith)
  let TP := P+(1+Q/r)*(P+r*Real.log (2*r))
  let TM := M+(1+N/r)*(M+r*Real.log (2*r))
  have hTp : 0 ≤ TP := by dsimp [TP]; positivity
  have hTm : 0 ≤ TM := by dsimp [TM]; positivity
  have hTPM : TP ≤ TM := by
    have hlt : P+r*Real.log (2*r) ≤ M+r*Real.log (2*r) := by linarith
    have hfac : (1+Q/r) ≤ (1+N/r) := by gcongr
    have hmul : (1+Q/r)*(P+r*Real.log (2*r)) ≤
        (1+N/r)*(M+r*Real.log (2*r)) := calc
      _ ≤ (1+Q/r)*(M+r*Real.log (2*r)) :=
        mul_le_mul_of_nonneg_left hlt (by positivity)
      _ ≤ _ :=
        mul_le_mul_of_nonneg_right hfac (by positivity)
    dsimp [TP,TM]
    linarith
  have ha : 0 ≤ A/M := by positivity
  have hb : 0 ≤ B/N := by positivity
  have ha2 : (Real.sqrt (A/M))^2 = A/M := Real.sq_sqrt ha
  have hb2 : (Real.sqrt (B/N))^2 = B/N := Real.sq_sqrt hb
  have ht2 : (Real.sqrt TP)^2 = TP := Real.sq_sqrt hTp
  have hbound' : s ≤
      5*Real.sqrt (A/M)*Real.sqrt (B/N)*Real.sqrt TP := hbound
  have hright0 : 0 ≤ 5*Real.sqrt (A/M)*Real.sqrt (B/N)*Real.sqrt TP := by
    positivity
  have hsq : s^2 ≤ 25*(A/M)*(B/N)*TP := by
    have hsq' := (sq_le_sq₀ hs hright0).mpr hbound'
    calc
      s^2 ≤ (5*Real.sqrt (A/M)*Real.sqrt (B/N)*Real.sqrt TP)^2 := hsq'
      _ = 25*(A/M)*(B/N)*TP := by
        rw [show (5*Real.sqrt (A/M)*Real.sqrt (B/N)*Real.sqrt TP)^2 =
          25*(Real.sqrt (A/M))^2*(Real.sqrt (B/N))^2*
            (Real.sqrt TP)^2 by ring,ha2,hb2,ht2]
  have hTM : (TM/(M*N)) ≤ 2*(1/N+1/r+
      Real.log (2*r)/M+r*Real.log (2*r)/(M*N)) := by
    dsimp [TM]
    exact source_minor_arc_scale_bound M N r (Real.log (2*r))
      hM hN hrpos hlog
  have hProd : 0 ≤ 25*A*B := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hTM hProd
  calc
    s^2 ≤ 25*(A/M)*(B/N)*TP := hsq
    _ ≤ 25*(A/M)*(B/N)*TM :=
      mul_le_mul_of_nonneg_left hTPM (by positivity)
    _ = 25*A*B*(TM/(M*N)) := by field_simp
    _ ≤ 25*A*B*(2*(1/N+1/r+Real.log (2*r)/M+
      r*Real.log (2*r)/(M*N))) := hScaled
    _ = _ := by ring
end Green64SourceC6

end

/-! ## SourceFrameScalarCancel -/

section

namespace Green64Analytic.CorrelationMellin

theorem scalar_schur_cancel (S B T : ℝ) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hFinal : S ^ 2 ≤ (B * T ^ 2) * S) : S ≤ B * T ^ 2 := by
  by_cases hs0 : S = 0
  · rw [hs0]
    exact mul_nonneg hB (sq_nonneg _)
  · have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hs0)
    exact le_of_mul_le_mul_right (by simpa only [pow_two] using hFinal) hpos
end Green64Analytic.CorrelationMellin

end

/-! ## SourceSparseGramFrame -/

section

open scoped InnerProductSpace ComplexConjugate

namespace Green64Analytic.CorrelationMellin

/-- Abstract separated-frequency frame bound from an honest Gram majorant. -/
theorem sparse_frame_bound
    {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (v : ι → E) (x : E) (K : ι → ι → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hG : ∀ i j, ‖⟪v i, v j⟫_ℂ‖ ≤ K i j)
    (hK : ∀ i j, 0 ≤ K i j)
    (hSym : ∀ i j, K i j = K j i)
    (hrow : ∀ i, ∑ j, K i j ≤ B) :
    (∑ i, ‖⟪v i, x⟫_ℂ‖ ^ 2) ≤ B * ‖x‖ ^ 2 := by
  classical
  let z : ι → ℂ := fun i => ⟪v i, x⟫_ℂ
  let q : E := ∑ i, z i • v i
  let S : ℝ := ∑ i, ‖z i‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hEval : ⟪q, x⟫_ℂ = (S : ℂ) := by
    dsimp [q, S]
    simp_rw [sum_inner, inner_smul_left]
    change (∑ i, (starRingEnd ℂ) (z i) * z i) =
      ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ)
    simp_rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    norm_cast
  have hGram : ‖q‖ ^ 2 ≤ B * S := by
    have hExpanded :
        (∑ i, ∑ j, ⟪v i, v j⟫_ℂ * star (z i) * z j) = ⟪q, q⟫_ℂ := by
      dsimp [q]
      simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hSchur := sparse_gram_complex_schur
      (Finset.univ : Finset ι)
      (fun i j => ⟪v i, v j⟫_ℂ) (fun i => star (z i)) K B
      (by intro i _ j _; exact hG i j)
      (by intro i _ j _; exact hK i j)
      (by intro i _ j _; exact hSym i j)
      (by intro i _; exact hrow i)
    have hBound :
        ‖∑ i, ∑ j, ⟪v i, v j⟫_ℂ * star (z i) * z j‖ ≤ B * S := by
      simpa only [star_star, norm_star, S] using hSchur
    calc
      ‖q‖ ^ 2 = ‖⟪q, q⟫_ℂ‖ := by
        rw [inner_self_eq_norm_sq_to_K]
        simp
      _ = ‖∑ i, ∑ j, ⟪v i, v j⟫_ℂ * star (z i) * z j‖ := by
        rw [hExpanded]
      _ ≤ B * S := hBound
  have hEvalNorm : S ≤ ‖q‖ * ‖x‖ := by
    calc
      S = ‖(S : ℂ)‖ := by
        rw [Complex.norm_real]
        exact (abs_of_nonneg hS).symm
      _ = ‖⟪q, x⟫_ℂ‖ := by rw [hEval]
      _ ≤ ‖q‖ * ‖x‖ := norm_inner_le_norm q x
  have hFinal : S ^ 2 ≤ (B * ‖x‖ ^ 2) * S := by
    calc
      _ ≤ (‖q‖ * ‖x‖) ^ 2 :=
        (sq_le_sq₀ hS (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hEvalNorm
      _ = ‖q‖ ^ 2 * ‖x‖ ^ 2 := by ring
      _ ≤ (B * S) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hGram (sq_nonneg _)
      _ = (B * ‖x‖ ^ 2) * S := by ring
  have hSle : S ≤ B * ‖x‖ ^ 2 :=
    scalar_schur_cancel S B ‖x‖ hS hB hFinal
  simpa only [S, z] using hSle

end Green64Analytic.CorrelationMellin

end

/-! ## SourceRealFrequencySparseFrame -/

section

/-!
The source-real-frequency Dirichlet polynomial, with no replacement of
its collapsed coefficient sequence or character support.  The only
analytic hypothesis is a Gram row majorant at the actual frequencies.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Green64Analytic.CorrelationMellin

/-- The genuine logarithmic real-frequency large sieve, conditional only
on a nonnegative symmetric row bound for its exact oscillatory kernel. -/
theorem source_real_frequency_frame
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (index : ν → ℕ) (t : ι → ℝ) (c : ν → ℂ)
    (K : ι → ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hK : ∀ i j, 0 ≤ K i j)
    (hSym : ∀ i j, K i j = K j i)
    (hG : ∀ i j, ‖∑ n : ν, sourcePhase (index n) (t i - t j)‖ ≤ K i j)
    (hrow : ∀ i, ∑ j, K i j ≤ B) :
    (∑ i : ι, ‖∑ n : ν, c n * sourcePhase (index n) (t i)‖ ^ 2) ≤
       B * ∑ n : ν, ‖c n‖ ^ 2 := by
  classical
  let x : EuclideanSpace ℂ ν := WithLp.toLp 2 c
  let v : ι → EuclideanSpace ℂ ν :=
    fun i => WithLp.toLp 2 (fun n => star (sourcePhase (index n) (t i)))
  have hinner (i : ι) :
      ⟪v i, x⟫_ℂ = ∑ n : ν, c n * sourcePhase (index n) (t i) := by
    simp [v, x, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hgram (i j : ι) :
      ⟪v i, v j⟫_ℂ = ∑ n : ν, sourcePhase (index n) (t i - t j) := by
    calc
      _ = ∑ n : ν,
          sourcePhase (index n) (t i) * star (sourcePhase (index n) (t j)) := by
            simp [v, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n _
        exact sourcePhase_conj_mul (index n) (t i) (t j)
  have hframe := sparse_frame_bound v x K B hB
    (by intro i j; rw [hgram]; exact hG i j) hK hSym hrow
  have hx : ‖x‖ ^ 2 = ∑ n : ν, ‖c n‖ ^ 2 := by
    simpa [x] using EuclideanSpace.norm_sq_eq x
  simpa only [hinner, hx] using hframe

end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualSparseR -/

section

/-!
Actual dyadic integer support version of the frequency-frame estimate.
`coeff n` is not changed or replaced: this interface accepts the exact
source-collapsed `alpha * residual` coefficient, with its original
character restrictions and its separately proved reciprocal L² norm.
-/

namespace Green64Analytic.CorrelationMellin

theorem source_integer_support_sparse_mean_square
    {ι : Type*} [Fintype ι]
    (s : Finset ℕ) (t : ι → ℝ) (coeff : ℕ → ℂ)
    (K : ι → ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hK : ∀ i j, 0 ≤ K i j)
    (hSym : ∀ i j, K i j = K j i)
    (hG : ∀ i j,
      ‖∑ n ∈ s, sourcePhase n (t i - t j)‖ ≤ K i j)
    (hrow : ∀ i, ∑ j, K i j ≤ B) :
    (∑ i : ι, ‖∑ n ∈ s, coeff n * sourcePhase n (t i)‖ ^ 2) ≤
      B * ∑ n ∈ s, ‖coeff n‖ ^ 2 := by
  classical
  let ν := {n : ℕ // n ∈ s}
  have hsum (f : ℕ → ℂ) :
      (∑ n ∈ s, f n) = ∑ n : ν, f n.val :=
    Finset.sum_subtype s (fun n => Iff.rfl) f
  have hG' (i j : ι) :
      ‖∑ n : ν, sourcePhase n.val (t i - t j)‖ ≤ K i j := by
    simpa only [hsum (fun n => sourcePhase n (t i - t j))] using hG i j
  have hf := source_real_frequency_frame (fun n : ν => n.val)
    t (fun n : ν => coeff n.val) K B hB hK hSym hG' hrow
  change (∑ i : ι, ‖∑ n : ν, coeff n.val * sourcePhase n.val (t i)‖ ^ 2) ≤
      B * ∑ n : ν, ‖coeff n.val‖ ^ 2 at hf
  have hsumR :
      (∑ n ∈ s, ‖coeff n‖ ^ 2) = ∑ n : ν, ‖coeff n.val‖ ^ 2 :=
    Finset.sum_subtype s (fun n => Iff.rfl) (fun n => ‖coeff n‖ ^ 2)
  calc
    _ = ∑ i : ι,
        ‖∑ n : ν, coeff n.val * sourcePhase n.val (t i)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hsum (fun n => coeff n * sourcePhase n (t i))]
    _ ≤ B * ∑ n : ν, ‖coeff n.val‖ ^ 2 := hf
    _ = B * ∑ n ∈ s, ‖coeff n‖ ^ 2 := by rw [hsumR]

end Green64Analytic.CorrelationMellin

end

/-! ## SourceFullBlockGramContract -/

section

/-!
Exact analytical debt for the source sparse real-frequency large sieve.
The Gram kernel is summed over the FULL integer dyadic block, not the
arbitrary support of the actual collapsed residual coefficients.
-/

namespace Green64Analytic.CorrelationMellin

/-- A single real-frequency Gram row bound is sufficient to obtain
the exact sparse L² estimate on a full integer block. -/
theorem source_full_integer_block_sparse_of_gram_rows
    {ι : Type*} [Fintype ι] (A Z : ℕ)
    (t : ι → ℝ) (coeff : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i : ι, ∑ j : ι,
      ‖∑ n ∈ Finset.Icc A Z, sourcePhase n (t i - t j)‖ ≤ B) :
    (∑ i : ι, ‖∑ n ∈ Finset.Icc A Z,
        coeff n * sourcePhase n (t i)‖ ^ 2) ≤
      B * ∑ n ∈ Finset.Icc A Z, ‖coeff n‖ ^ 2 := by
  classical
  let s := Finset.Icc A Z
  let K : ι → ι → ℝ :=
    fun i j => ‖∑ n ∈ s, sourcePhase n (t i - t j)‖
  have hK (i j : ι) : 0 ≤ K i j := norm_nonneg _
  have hSym (i j : ι) : K i j = K j i := by
    dsimp [K]
    have hstar :
        (∑ n ∈ s, sourcePhase n (t j - t i)) =
          star (∑ n ∈ s, sourcePhase n (t i - t j)) := by
      calc
        _ = ∑ n ∈ s, star (sourcePhase n (t i - t j)) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [← sourcePhase_neg]
          congr 1
          ring
        _ = _ := by simp only [Complex.star_def, map_sum]
    rw [hstar, norm_star]
  have hG (i j : ι) :
      ‖∑ n ∈ s, sourcePhase n (t i - t j)‖ ≤ K i j := le_refl _
  have hrow' (i : ι) : ∑ j : ι, K i j ≤ B := hrow i
  exact source_integer_support_sparse_mean_square s t coeff K B
    hB hK hSym hG hrow'
end Green64Analytic.CorrelationMellin

end

/-! ## SourceExceptionalFullBlock -/

section

/-!
Actual exceptional-frequency cardinal bound from a SINGLE oscillatory
Gram-row hypothesis on the full consecutive integer block [1,Y].
No assumption on a Gram kernel restricted to product support.
-/

namespace Green64Analytic.CorrelationMellin

theorem source_exceptional_count_from_full_block_gram
    {ι : Type*} [Fintype ι] (times : ι → ℝ)
    (s : Finset ℕ) (j Y : ℕ) (hprime : ∀ p ∈ s, Nat.Prime p)
    (w : {p : ℕ // p ∈ s} → ℂ) (δ B : ℝ)
    (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hSupport : sourcePrimePowerSupport s j ⊆ Finset.Icc 1 Y)
    (hlarge : ∀ i : ι,
      δ ≤ ‖∑ p : {p : ℕ // p ∈ s}, w p * sourcePhase p.val (times i)‖)
    (hrows : ∀ i : ι, ∑ k : ι,
      ‖∑ n ∈ Finset.Icc 1 Y, sourcePhase n (times i - times k)‖ ≤ B) :
    (Fintype.card ι : ℝ) * δ ^ (2*j) ≤
      B * ((j.factorial : ℝ) *
        (∑ p : {p : ℕ // p ∈ s}, ‖w p‖ ^ 2) ^ j) := by
  classical
  let support := sourcePrimePowerSupport s j
  let coeff : ℕ → ℂ := sourcePrimePowerCoefficients s j w
  let padded : ℕ → ℂ := fun n => if n ∈ support then coeff n else 0
  have hPad (φ : ℕ → ℂ) :
      (∑ n ∈ Finset.Icc 1 Y, padded n * φ n) =
        ∑ n ∈ support, coeff n * φ n := by
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
      (∑ n ∈ Finset.Icc 1 Y, ‖padded n‖ ^ 2) =
        ∑ n ∈ support, ‖coeff n‖ ^ 2 := by
    calc
      _ = ∑ n ∈ support, ‖padded n‖ ^ 2 := by
        symm
        apply Finset.sum_subset hSupport
        intro n hn hnS
        have hsNot : n ∉ support := hnS
        simp [padded, hsNot]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [padded, hn]
  have hFrame := source_full_integer_block_sparse_of_gram_rows
    (ι := ι) 1 Y times padded B hB hrows
  have hSparse :
      (∑ i : ι,
        ‖∑ n ∈ support, coeff n * sourcePhase n (times i)‖ ^ 2) ≤
        B * ∑ n ∈ support, ‖coeff n‖ ^ 2 := by
    calc
      _ = ∑ i : ι,
          ‖∑ n ∈ Finset.Icc 1 Y, padded n * sourcePhase n (times i)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hPad]
      _ ≤ B * ∑ n ∈ Finset.Icc 1 Y, ‖padded n‖ ^ 2 := hFrame
      _ = _ := by rw [hPadNorm]
  have hCount := source_exceptional_count_of_power_evaluation
    (Finset.univ : Finset ι) times s j hprime w δ B hδ hB
    (by intro i _; exact hlarge i) hSparse
  simpa [support, coeff] using hCount
end Green64Analytic.CorrelationMellin

end

/-! ## SourceExceptionalLogCount -/

section

/-!
The source exceptional count with exact j0=floor(log Y/log(2P)), genuine
prime coefficients b_s(p)/p, growing factorial, and full-block Gram rows.
Only the oscillatory analytic Gram estimate is an assumption.
-/

namespace Green64Analytic.CorrelationMellin

theorem source_exceptional_log_order_count_of_full_gram
    {ι : Type*} [Fintype ι] (times : ι → ℝ)
    (s : Finset ℕ) (P Y : ℕ) (C δ B : ℝ)
    (hP : 1 ≤ P) (hY : 1 ≤ Y)
    (hprime : ∀ p ∈ s, Nat.Prime p)
    (hSupport : s ⊆ Finset.Icc P (2*P))
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (b : ℕ → ℂ) (hb : ∀ p ∈ s, ‖b p‖ ≤ C)
    (hlarge : ∀ i : ι,
      δ ≤ ‖∑ p : {p : ℕ // p ∈ s},
        (b p.val * ((p.val:ℂ)⁻¹)) * sourcePhase p.val (times i)‖)
    (hrows : ∀ i : ι, ∑ k : ι,
      ‖∑ n ∈ Finset.Icc 1 Y, sourcePhase n (times i - times k)‖ ≤ B) :
    (Fintype.card ι : ℝ) * δ ^ (2*(sourcePrimeMomentOrder P Y)) ≤
      B * ((Nat.factorial (sourcePrimeMomentOrder P Y) : ℝ) *
        (2*C^2/(P:ℝ))^(sourcePrimeMomentOrder P Y)) := by
  classical
  let j := sourcePrimeMomentOrder P Y
  let w : {p : ℕ // p ∈ s} → ℂ :=
    fun p => b p.val * ((p.val:ℂ)⁻¹)
  have hPow : (2*P)^j ≤ Y :=
    (source_prime_moment_order_power_bounds P Y hP hY).1
  have hFull : sourcePrimePowerSupport s j ⊆ Finset.Icc 1 Y :=
    source_prime_power_support_within_Y s j P Y hP hSupport hPow
  have hSq : (∑ p : {p : ℕ // p ∈ s}, ‖w p‖ ^ 2) ≤
      2*C^2/(P:ℝ) := by
    have heq : (∑ p : {p : ℕ // p ∈ s}, ‖w p‖ ^ 2) =
        ∑ p ∈ s, ‖b p * ((p:ℂ)⁻¹)‖ ^ 2 := by
      simpa only [w] using (Finset.sum_subtype s (fun p => Iff.rfl)
        (fun p => ‖b p * ((p:ℂ)⁻¹)‖ ^ 2)).symm
    rw [heq]
    exact source_short_prime_reciprocal_square_budget s P C b
      hP hC hSupport hb
  have hPowSq :
      (∑ p : {p : ℕ // p ∈ s}, ‖w p‖ ^ 2)^j ≤
        (2*C^2/(P:ℝ))^j := by
    gcongr
  have hCount := source_exceptional_count_from_full_block_gram
    times s j Y hprime w δ B hδ hB hFull
    (by intro i; exact hlarge i) hrows
  calc
    _ ≤ B * ((j.factorial : ℝ) *
        (∑ p : {p : ℕ // p ∈ s}, ‖w p‖ ^ 2)^j) := hCount
    _ ≤ B * ((j.factorial : ℝ) * (2*C^2/(P:ℝ))^j) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact mul_le_mul_of_nonneg_left hPowSq (Nat.cast_nonneg _)
end Green64Analytic.CorrelationMellin

end

/-! ## SourceGenericDominatedContinuous -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare

/-- Independently elaborated dominated-parameter-continuity interface.
The real source kernel is instantiated in a separate module. -/
theorem source_generic_dominated_continuity434
    (F : ℝ → ℝ → ℂ) (bound : ℝ → ℝ)
    (hb : Integrable bound)
    (hm : ∀ u : ℝ, AEStronglyMeasurable (F u))
    (hd : ∀ u : ℝ, ∀ᵐ t ∂(volume : Measure ℝ), ‖F u t‖ ≤ bound t)
    (hc : ∀ t : ℝ, Continuous (fun u : ℝ => F u t)) :
    Continuous (fun u : ℝ => ∫ t : ℝ, F u t) := by
  exact continuous_of_dominated hm hd hb
    (Filter.Eventually.of_forall hc)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceGenericL2NormIntegral -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 700000

/-- Exact L² norm-square versus the genuine whole-real-line squared
Bochner integral, without default-zero on a non-integrable function. -/
theorem source_generic_L2_norm_sq434
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume : Measure ℝ)) :
    ‖MemLp.toLp f hf‖^2 =
      ∫ x : ℝ, ‖f x‖^2 := by
  have hi := (memLp_two_iff_integrable_sq_norm
    hf.aestronglyMeasurable).mp hf
  have hp : 0 ≤ (∫ x : ℝ, ‖f x‖^2) :=
    integral_nonneg (fun x => sq_nonneg _)
  calc
    ‖MemLp.toLp f hf‖^2 =
      ((∫ x : ℝ, ‖f x‖^2)^(1/2:ℝ))^2 := by
      rw [Lp.norm_toLp, toReal_eLpNorm,
        lpNorm_eq_integral_norm_rpow_toReal
          (by norm_num : (2:ENNReal) ≠ 0)
          (by norm_num : (2:ENNReal) ≠ ⊤)
          hf.aestronglyMeasurable]
      norm_num
    _ = _ := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sq_sqrt hp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceGenericClassicalPlancherel -/

section

open MeasureTheory
open scoped FourierTransform
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 950000

/-- Fully kernel-checked CLASSICAL whole-real Plancherel for f∈L¹∩L²
with classical Fourier f∈L². Derived from Fourier's L² isometry,
the genuine L¹/L² tempered-distribution compatibility and explicit
Bochner-square normalization. Not a source energy-saving assumption. -/
theorem source_generic_classical_plancherel434
    (f : ℝ → ℂ) (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hF2 : MemLp (𝓕 f) 2 (volume : Measure ℝ)) :
    (∫ x : ℝ, ‖f x‖^2) =
      ∫ s : ℝ, ‖(𝓕 f) s‖^2 := by
  let F2 : Lp ℂ 2 (volume : Measure ℝ) := MemLp.toLp f hf2
  let G2 : Lp ℂ 2 (volume : Measure ℝ) := MemLp.toLp (𝓕 f) hF2
  have hcompat := source_L1L2_fourier_compat434 f hf1 hf2 hF2
  calc
    _ = ‖F2‖^2 := (source_generic_L2_norm_sq434 f hf2).symm
    _ = ‖𝓕 F2‖^2 := by rw [Lp.norm_fourier_eq]
    _ = ‖G2‖^2 := by
      exact (congrArg (fun z : Lp ℂ 2 (volume : Measure ℝ) => ‖z‖^2)
        hcompat).symm
    _ = _ := source_generic_L2_norm_sq434 (𝓕 f) hF2
end Green64Analytic.CorrelationSquare

end

/-! ## SourceIntervalKernel -/

section

namespace Green64SourceC6

/-- Phase translation is exact for any integer starting address. -/
theorem translated_phase_geometric (theta : ℝ) (start : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.range N, integerPhase theta (start + (n : ℤ))) =
      integerPhase theta start *
      (∑ n ∈ Finset.range N, (integerPhase theta 1)^n) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [integerPhase_add, integerPhase_nat]

/-- The literal whole-integer-interval exponential kernel, with no
centered interval, smoothness, or missing-coefficient assumptions. -/
theorem translated_additive_kernel (theta : ℝ) (start : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, integerPhase theta (start + (n : ℤ))‖ ≤ (N : ℝ) ∧
    ‖1 - integerPhase theta 1‖ *
      ‖∑ n ∈ Finset.range N, integerPhase theta (start + (n : ℤ))‖ ≤ 2 := by
  have hnorm :
      ‖∑ n ∈ Finset.range N, integerPhase theta (start + (n : ℤ))‖ =
      ‖∑ n ∈ Finset.range N, (integerPhase theta 1)^n‖ := by
    rw [translated_phase_geometric, norm_mul, integerPhase_unit, one_mul]
  have hgeom := geometric_unit_kernel (integerPhase theta 1) N
      (integerPhase_unit theta 1)
  constructor
  · rw [hnorm]
    exact hgeom.1
  · rw [hnorm]
    exact hgeom.2

end Green64SourceC6

end

/-! ## ShortArcGeometric -/

section

namespace Green64SourceC6

/-- Source-exact rational-approximation lower bound for a short difference d.
Includes the nearest integer and the full complex exponential chord. -/
theorem short_rational_chord_lower
    (a r d : ℤ) (beta : ℝ)
    (hr : 0 < r) (hd : 0 < d) (hhalf : 2 * d ≤ r)
    (hcop : Int.gcd a r = 1)
    (hbeta : |beta| ≤ 1 / ((r : ℝ)^2)) :
    (2 : ℝ)/(r : ℝ) ≤
      ‖1 - integerPhase (((a : ℝ)/(r : ℝ)+beta)*(d : ℝ)) 1‖ := by
  let theta := ((a : ℝ)/(r : ℝ)+beta)*(d : ℝ)
  obtain ⟨z, hdist, hchord⟩ := nearest_integer_chord theta
  have hsep : (1 : ℝ)/(2*(r : ℝ)) ≤ |theta - (z : ℝ)| :=
    short_rational_arc_separation a r d z beta hr hd hhalf hcop hbeta
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have heq : (2 : ℝ)/(r : ℝ) = 4 * (1/(2*(r : ℝ))) := by
    field_simp
    norm_num
  calc
    (2 : ℝ)/(r : ℝ) = 4 * (1/(2*(r : ℝ))) := heq
    _ ≤ 4 * |theta - (z : ℝ)| := by gcongr
    _ ≤ ‖1 - integerPhase theta 1‖ := hchord

/-- A genuine source geometric kernel saving on short rational differences;
this theorem does not yet sum over all differences. -/
theorem short_rational_geometric_bound
    (a r d : ℤ) (beta : ℝ) (start : ℤ) (N : ℕ)
    (hr : 0 < r) (hd : 0 < d) (hhalf : 2 * d ≤ r)
    (hcop : Int.gcd a r = 1)
    (hbeta : |beta| ≤ 1 / ((r : ℝ)^2)) :
    ‖∑ n ∈ Finset.range N,
      integerPhase (((a : ℝ)/(r : ℝ)+beta)*(d : ℝ)) (start + (n : ℤ))‖ ≤
      (r : ℝ) := by
  let theta := ((a : ℝ)/(r : ℝ)+beta)*(d : ℝ)
  let S := ∑ n ∈ Finset.range N, integerPhase theta (start + (n : ℤ))
  have hch : (2 : ℝ)/(r : ℝ) ≤ ‖1 - integerPhase theta 1‖ :=
    short_rational_chord_lower a r d beta hr hd hhalf hcop hbeta
  have hgeom : ‖1 - integerPhase theta 1‖ * ‖S‖ ≤ 2 :=
    (translated_additive_kernel theta start N).2
  have hm : ((2 : ℝ)/(r : ℝ)) * ‖S‖ ≤ 2 :=
    (mul_le_mul_of_nonneg_right hch (norm_nonneg S)).trans hgeom
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hf : (0 : ℝ) < (2 : ℝ)/(r : ℝ) := by positivity
  have hrat : ‖S‖ ≤ 2 / ((2 : ℝ)/(r : ℝ)) := by
    apply (le_div_iff₀ hf).mpr
    simpa [mul_comm] using hm
  have heq : (2 : ℝ)/((2 : ℝ)/(r : ℝ)) = (r : ℝ) := by
    field_simp
  exact hrat.trans_eq heq

end Green64SourceC6

end

/-! ## C6PhaseKernel -/

section

namespace Green64SourceC6

/-- A genuine source exponential phase differs from its fractional phase
by an integer frequency, hence the complex factors are identical. -/
theorem source_phase_frac_period (alpha : ℝ) (d : ℤ) :
    integerPhase (fracPhase alpha d) 1 =
      integerPhase (alpha * (d : ℝ)) 1 := by
  simpa only [fracPhase] using
    (integerPhase_frequency_period (alpha * (d : ℝ))
      (⌊alpha * (d : ℝ)⌋))

theorem source_fractional_chord (alpha : ℝ) (d : ℤ) :
    4 * min (fracPhase alpha d) (1-fracPhase alpha d) ≤
      ‖1 - integerPhase (alpha * (d : ℝ)) 1‖ := by
  let v := fracPhase alpha d
  have hv := fracPhase_range alpha d
  by_cases hhalf : v ≤ 1/2
  · have hh := fundamental_chord_lower v hv.1 hhalf
    rw [min_eq_left (by linarith : v ≤ 1-v)]
    simpa only [v, source_phase_frac_period] using hh
  · have hv1 : v - 1 ≤ 0 := by linarith [hv.2]
    have habs : |v-1| ≤ 1/2 := by
      rw [abs_of_nonpos hv1]
      linarith
    have hh := signed_fundamental_chord_lower (v-1) habs
    have hper : integerPhase (v-1) 1 = integerPhase v 1 := by
      simpa using integerPhase_frequency_period v 1
    rw [hper] at hh
    rw [abs_of_nonpos hv1] at hh
    rw [min_eq_right (by linarith : 1-v ≤ v)]
    have hh' : 4*(1-v) ≤ ‖1 - integerPhase v 1‖ := by
      convert hh using 1 <;> ring
    simpa only [v, source_phase_frac_period] using hh'

/-- The nonvanishing chord parameter is *derived*, not imposed on the
original coefficients or on the bilinear phase. -/
theorem source_geometric_le_of_chord (theta : ℝ) (start : ℤ)
    (N : ℕ) (delta : ℝ) (hd : 0 < delta)
    (hch : 4*delta ≤ ‖1 - integerPhase theta 1‖) :
    ‖∑ j ∈ Finset.range N,
        integerPhase theta (start + (j : ℤ))‖ ≤ 1/(2*delta) := by
  let S := ∑ j ∈ Finset.range N,
        integerPhase theta (start + (j : ℤ))
  have hgeom := (translated_additive_kernel theta start N).2
  have hbound : 4*delta * ‖S‖ ≤ 2 :=
    (mul_le_mul_of_nonneg_right hch (norm_nonneg S)).trans hgeom
  have hd2 : 0 < 2*delta := by positivity
  apply (le_div_iff₀ hd2).2
  dsimp [S] at *
  nlinarith

end Green64SourceC6

end

/-! ## C6CellKernel -/

section

namespace Green64SourceC6

theorem translated_kernel_by_phase_cell
    (alpha : ℝ) (d M : ℤ) (P : ℕ) (lo hi : ℝ)
    (hlo : 0 < lo) (hhi : 0 < hi)
    (hvlo : lo ≤ fracPhase alpha d)
    (hvhi : hi ≤ 1 - fracPhase alpha d) :
    ‖∑ m ∈ Finset.range P,
        integerPhase (alpha*(d : ℝ)) (M+(m : ℤ))‖ ≤
      1/(2*lo) + 1/(2*hi) := by
  have hm : 0 < min lo hi := lt_min hlo hhi
  have hd : min lo hi ≤ min (fracPhase alpha d)
      (1 - fracPhase alpha d) := min_le_min hvlo hvhi
  have hchord := source_fractional_chord alpha d
  have hch : 4 * min lo hi ≤
      ‖1 - integerPhase (alpha*(d:ℝ)) 1‖ := by
    linarith
  have hk := source_geometric_le_of_chord
    (alpha*(d:ℝ)) M P (min lo hi) hm hch
  rcases le_total lo hi with h | h
  · rw [min_eq_left h] at hk
    have hp : 0 ≤ 1/(2*hi) := by positivity
    linarith
  · rw [min_eq_right h] at hk
    have hp : 0 ≤ 1/(2*lo) := by positivity
    linarith
/-- Inside the j=k+1 bin, the literal translated geometric kernel
has the two reciprocal interior-distance envelopes. -/
theorem source_inner_phase_cell_kernel
    (alpha : ℝ) (d M : ℤ) (P n k : ℕ)
    (hk : k < n)
    (hcell : sourcePhaseBin (n+2) alpha d = k+1) :
    ‖∑ m ∈ Finset.range P,
        integerPhase (alpha*(d : ℝ)) (M+(m : ℤ))‖ ≤
      harmonicBinWeight n (P : ℝ) (k+1) := by
  let r : ℕ := n+2
  let v := fracPhase alpha d
  have hr : 0 < r := by dsimp [r]; omega
  have hc := sourcePhaseBin_cell r alpha d hr
  rw [hcell] at hc
  have hlow : ((k+1 : ℕ) : ℝ)/(r:ℝ) ≤ v := hc.1
  have hhigh : v < ((k+1+1 : ℕ) : ℝ)/(r:ℝ) := hc.2
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hk1 : (0 : ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
  have hnk : (0 : ℝ) < ((n-k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n-k)
  have hsum : ((n-k : ℕ) : ℝ) + ((k+1+1 : ℕ) : ℝ) = (r : ℝ) := by
    exact_mod_cast (show n-k + (k+1+1) = r by dsimp [r]; omega)
  have hunit : ((n-k : ℕ) : ℝ)/(r:ℝ) +
      ((k+1+1 : ℕ) : ℝ)/(r:ℝ) = 1 := by
    rw [← add_div, hsum]
    field_simp
  have hupper : ((n-k : ℕ) : ℝ)/(r:ℝ) ≤ 1-v := by
    linarith
  have hlopos : 0 < ((k+1 : ℕ) : ℝ)/(r:ℝ) := div_pos hk1 hrpos
  have hhipos : 0 < ((n-k : ℕ) : ℝ)/(r:ℝ) := div_pos hnk hrpos
  have hh := translated_kernel_by_phase_cell alpha d M P
    (((k+1 : ℕ) : ℝ)/(r:ℝ)) (((n-k : ℕ) : ℝ)/(r:ℝ))
    hlopos hhipos hlow hupper
  rw [harmonicBinWeight_inner n k (P:ℝ) hk]
  dsimp [r] at hh ⊢
  have hden1 : ((k+1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hk1
  have hden2 : ((n-k : ℕ) : ℝ) ≠ 0 := ne_of_gt hnk
  have hrne : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hid :
      1/(2*(((k+1 : ℕ) : ℝ)/((n+2:ℕ):ℝ))) +
      1/(2*(((n-k:ℕ):ℝ)/((n+2:ℕ):ℝ))) =
      (((n+2 : ℕ) : ℝ)/2) *
       ((((k+1 : ℕ) : ℝ)⁻¹) + (((n-k : ℕ) : ℝ)⁻¹)) := by
    field_simp
  exact hh.trans_eq hid

end Green64SourceC6

end

/-! ## C6ShortBlock -/

section

namespace Green64SourceC6

/-- Complete genuine short-block C6 sum, on any translated or sparse set
of integer differences, with the literal coprime rational approximation. -/
theorem source_short_phase_block
    (a : ℤ) (n : ℕ) (beta : ℝ)
    (s : Finset ℤ) (M : ℤ) (P : ℕ)
    (hcop : Int.gcd a ((n+2 : ℕ) : ℤ) = 1)
    (hbeta : |beta| ≤ 1 / ((((n+2 : ℕ) : ℝ))^2))
    (hshort : ∀ d ∈ s, ∀ e ∈ s,
      2 * |e-d| ≤ ((n+2 : ℕ) : ℤ)) :
    (∑ d ∈ s,
      ‖∑ m ∈ Finset.range P,
        integerPhase (((a : ℝ)/((n+2:ℕ):ℝ)+beta)*(d:ℝ))
          (M+(m:ℤ))‖) ≤
      4 * ((P : ℝ) + ((n+2 : ℕ) : ℝ) *
        Real.log (2 * ((n+2 : ℕ) : ℝ))) := by
  let r := n+2
  let alpha : ℝ := (a : ℝ)/(r:ℝ)+beta
  let bin := sourcePhaseBin r alpha
  let f := fun d : ℤ =>
      ‖∑ m ∈ Finset.range P,
        integerPhase (alpha*(d:ℝ)) (M+(m:ℤ))‖
  let w := harmonicBinWeight n (P:ℝ)
  have hr : 0 < r := by dsimp [r]; omega
  have hin : ∀ d ∈ s, bin d < r := by
    intro d hd
    exact sourcePhaseBin_lt r alpha d hr
  have hcap : ∀ j ∈ Finset.range r,
      (s.filter (fun d => bin d = j)).card ≤ 2 := by
    intro j hj
    exact sourcePhaseBin_card_le_two a r beta s hr
      (by simpa only [r] using hcop)
      (by simpa only [r] using hbeta)
      (by simpa only [r] using hshort) j
  have hw : ∀ j ∈ Finset.range r, 0 ≤ w j := by
    intro j hj
    exact harmonicBinWeight_nonneg n (P:ℝ) (by positivity) j
  have hf : ∀ d ∈ s, f d ≤ w (bin d) := by
    intro d hd
    let j := bin d
    have hj : j < n+2 := by simpa only [r] using hin d hd
    by_cases hz : j = 0
    · have h := (translated_additive_kernel (alpha*(d:ℝ)) M P).1
      simpa only [f, w, j, hz, harmonicBinWeight_zero] using h
    · by_cases he : j = n+1
      · have h := (translated_additive_kernel (alpha*(d:ℝ)) M P).1
        simpa only [f, w, j, he, harmonicBinWeight_last] using h
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hz
        have hjlo : j < n+1 := by omega
        let k := j-1
        have hk : k < n := by dsimp [k]; omega
        have hk_eq : j = k+1 := by dsimp [k]; omega
        have hh := source_inner_phase_cell_kernel alpha d M P n k hk
          (by simpa only [bin, j, hk_eq] using
            (show sourcePhaseBin (n+2) alpha d = k+1 by
              change j = k+1
              exact hk_eq))
        simpa only [f, w, j, hk_eq] using hh
  have hsum := sum_le_two_bin_weights r s bin f w hin hcap hf hw
  have hbudget := harmonicBinWeight_sum_bound n (P:ℝ) (by positivity)
  change (∑ d ∈ s, f d) ≤
    4 * ((P : ℝ) + ((n+2 : ℕ) : ℝ) *
        Real.log (2 * ((n+2 : ℕ) : ℝ)))
  exact hsum.trans (by simpa only [r, w] using hbudget)

end Green64SourceC6

end

/-! ## C6NatBlocks -/

section

namespace Green64SourceC6

theorem source_short_nat_phase_block
    (a : ℤ) (n : ℕ) (beta : ℝ)
    (s : Finset ℕ) (M : ℤ) (P : ℕ)
    (hcop : Int.gcd a ((n+2 : ℕ) : ℤ) = 1)
    (hbeta : |beta| ≤ 1 / ((((n+2 : ℕ) : ℝ))^2))
    (hshort : ∀ d ∈ s, ∀ e ∈ s,
      2 * |((e : ℤ)-(d : ℤ))| ≤ ((n+2 : ℕ) : ℤ)) :
    (∑ d ∈ s,
      ‖∑ m ∈ Finset.range P,
        integerPhase (((a : ℝ)/((n+2:ℕ):ℝ)+beta)*(d:ℝ))
          (M+(m:ℤ))‖) ≤
      4 * ((P : ℝ) + ((n+2 : ℕ) : ℝ) *
        Real.log (2 * ((n+2 : ℕ) : ℝ))) := by
  classical
  let si : Finset ℤ := s.image (fun d : ℕ => (d : ℤ))
  have hi : ∀ d ∈ si, ∀ e ∈ si,
      2*|e-d| ≤ (((n+2:ℕ) : ℤ)) := by
    intro d hd e he
    rcases Finset.mem_image.mp hd with ⟨d0,hds, rfl⟩
    rcases Finset.mem_image.mp he with ⟨e0,hes, rfl⟩
    exact hshort d0 hds e0 hes
  have hh := source_short_phase_block a n beta si M P
    hcop hbeta hi
  have hinj : Set.InjOn (fun d : ℕ => (d:ℤ)) (s : Set ℕ) := by
    intro d hd e he heq
    exact Int.ofNat_inj.mp heq
  rw [Finset.sum_image hinj] at hh
  simpa only [Int.cast_natCast] using hh

end Green64SourceC6

end

/-! ## C6GlobalDifferences -/

section

namespace Green64SourceC6

/-- Exact finite partition into quotient blocks: no overlap or missing
integer coefficient supports. -/
theorem sum_partition_by_nat_bin (s : Finset ℕ) (R : ℕ)
    (bin : ℕ → ℕ) (f : ℕ → ℝ)
    (hin : ∀ d ∈ s, bin d < R) :
    (∑ d ∈ s, f d) =
      ∑ j ∈ Finset.range R,
        ∑ d ∈ s.filter (fun d => bin d = j), f d := by
  classical
  calc
    _ = ∑ d ∈ s, ∑ j ∈ Finset.range R,
          if bin d = j then f d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_ite_eq]
      simp [hin d hd]
    _ = ∑ j ∈ Finset.range R, ∑ d ∈ s,
          if bin d = j then f d else 0 := Finset.sum_comm
    _ = _ := by simp_rw [Finset.sum_filter]

/-- An exact interval bin is short in the sense needed by the
rational phase separation theorem, including all translated groups. -/
theorem quotient_bin_short
    (r Q j : ℕ) (hr : 2 ≤ r)
    (s : Finset ℕ)
    (hS : ∀ d ∈ s, 1 ≤ d)
    (hbin : ∀ d ∈ s, (d-1)/(r/2) = j) :
    ∀ d ∈ s, ∀ e ∈ s,
       2 * |((e : ℤ)-(d : ℤ))| ≤ (r : ℤ) := by
  let B := r/2
  have hBpos : 0 < B := by dsimp [B]; omega
  have htwice : 2*B ≤ r := by
    dsimp [B]
    exact Nat.mul_div_le r 2
  have hloc (d : ℕ) (hd : d ∈ s) :
      B*j + 1 ≤ d ∧ d ≤ B*j+B := by
    have hdpos : 1 ≤ d := hS d hd
    have hdiv := hbin d hd
    have hstart := Nat.mul_div_le (d-1) B
    have hend := Nat.lt_mul_div_succ (d-1) hBpos
    rw [hdiv] at hstart hend
    have hend' : d-1 < B*j+B := by
      simpa [mul_add] using hend
    constructor <;> omega
  intro d hd e he
  obtain ⟨hdlo,hdhi⟩ := hloc d hd
  obtain ⟨helo,hehi⟩ := hloc e he
  have hp : ((e:ℤ)-(d:ℤ)) ≤ ((B:ℤ)-1) := by
    omega
  have hn : -((B:ℤ)-1) ≤ ((e:ℤ)-(d:ℤ)) := by
    omega
  have habs : |((e:ℤ)-(d:ℤ))| ≤ (B:ℤ)-1 :=
    abs_le.mpr ⟨hn,hp⟩
  have hBn : 1 ≤ B := by omega
  have hBreal : 2*((B:ℤ)-1) ≤ (r:ℤ) := by
    exact_mod_cast (show 2*(B-1) ≤ r by omega)
  omega

/-- Sum of translated integer geometric kernels over all positive
differences. This is the full C6 logarithmic block budget. -/
theorem source_global_positive_difference_sum
    (a : ℤ) (r Q P : ℕ) (beta : ℝ) (M : ℤ)
    (hr : 2 ≤ r)
    (hcop : Int.gcd a (r : ℤ) = 1)
    (hbeta : |beta| ≤ 1 / ((r : ℝ)^2)) :
    (∑ d ∈ Finset.Ico 1 Q,
       ‖∑ m ∈ Finset.range P,
          integerPhase (((a:ℝ)/(r:ℝ)+beta)*(d:ℝ)) (M+(m:ℤ))‖) ≤
      12 * (1+(Q:ℝ)/(r:ℝ)) *
        ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ))) := by
  classical
  let B := r/2
  let S := Finset.Ico 1 Q
  let R := (Q-1)/B+1
  let bin := fun d : ℕ => (d-1)/B
  let alpha : ℝ := (a:ℝ)/(r:ℝ)+beta
  let f := fun d : ℕ =>
       ‖∑ m ∈ Finset.range P,
           integerPhase (alpha*(d:ℝ)) (M+(m:ℤ))‖
  let C : ℝ := (P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ))
  have hBpos : 0 < B := by dsimp [B]; omega
  have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0< r)
  have hR : ∀ d ∈ S, bin d < R := by
    intro d hd
    have hd' : d-1 ≤ Q-1 := by
      have hdm := Finset.mem_Ico.mp hd
      omega
    have hs := Nat.div_le_div_right (c:=B) hd'
    dsimp [bin,R]
    omega
  have hSpos : ∀ d ∈ S, 1 ≤ d := by
    intro d hd
    exact (Finset.mem_Ico.mp hd).1
  have hb (j : ℕ) (hj : j ∈ Finset.range R) :
      (∑ d ∈ S.filter (fun d => bin d = j), f d) ≤ 4*C := by
    let t := S.filter (fun d => bin d = j)
    have hshort := quotient_bin_short r Q j hr t
      (by intro d hd; exact hSpos d (Finset.mem_filter.mp hd).1)
      (by intro d hd; exact (Finset.mem_filter.mp hd).2)
    have hn : (r-2)+2=r := by omega
    have hh := source_short_nat_phase_block a (r-2) beta t M P
      (by simpa [hn] using hcop) (by simpa [hn] using hbeta)
      (by simpa [hn] using hshort)
    simpa only [t, C, hn, alpha, f] using hh
  have hpart := sum_partition_by_nat_bin S R bin f hR
  have hsum : (∑ d ∈ S, f d) ≤ (R:ℝ)*(4*C) := by
    calc
      _ = ∑ j ∈ Finset.range R, ∑ d ∈ S.filter (fun d => bin d = j), f d := hpart
      _ ≤ ∑ j ∈ Finset.range R, 4*C := by
        apply Finset.sum_le_sum
        intro j hj
        exact hb j hj
      _ = (R:ℝ)*(4*C) := by simp
  have hBscale : r ≤ 3*B := by dsimp [B]; omega
  have hQ : B*((Q-1)/B) ≤ Q := by
    have hh := Nat.mul_div_le (Q-1) B
    omega
  have hRscale : (R:ℝ) ≤ 3*(1+(Q:ℝ)/(r:ℝ)) := by
    have hmul : ((r:ℝ))*(((Q-1)/B : ℕ):ℝ) ≤ 3*(Q:ℝ) := by
      have h0 : (0:ℝ) ≤ (((Q-1)/B : ℕ):ℝ) := by positivity
      have hBscale' : (r:ℝ) ≤ 3*(B:ℝ) := by exact_mod_cast hBscale
      have hQ' : (B:ℝ)*(((Q-1)/B : ℕ):ℝ) ≤ (Q:ℝ) := by
        exact_mod_cast hQ
      nlinarith [mul_le_mul_of_nonneg_right hBscale' h0]
    have hcast : (R:ℝ) = (((Q-1)/B : ℕ):ℝ)+1 := by
      simp only [R, Nat.cast_add, Nat.cast_one]
    have hprod : (r:ℝ)*(R:ℝ) ≤ 3*((r:ℝ)+(Q:ℝ)) := by
      rw [hcast]
      nlinarith [hmul]
    calc
      (R:ℝ) ≤ 3*((r:ℝ)+(Q:ℝ))/(r:ℝ) :=
        (le_div_iff₀ hrpos).2 (by simpa [mul_comm] using hprod)
      _ = 3*(1+(Q:ℝ)/(r:ℝ)) := by
        field_simp
  have hCpos : 0 ≤ C := by
    have hlog : 0 ≤ Real.log (2*(r:ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*r by omega))
    dsimp [C]
    positivity
  have hh : (R:ℝ)*(4*C) ≤
      12*(1+(Q:ℝ)/(r:ℝ))*C := by
    have hp : 0 ≤ 4*C := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hRscale hp]
  exact (by simpa only [S,alpha,f,C] using hsum.trans hh)

end Green64SourceC6

end

/-! ## C6RowBudget -/

section

namespace Green64SourceC6

/-- Exact number of occurrences of a positive distance in a translated row. -/
theorem nat_distance_row_identity (g : ℕ → ℝ)
    (Q j : ℕ) (hj : j < Q) :
    (∑ k ∈ Finset.range Q, g (Nat.dist j k)) =
      g 0 + (∑ d ∈ Finset.Ico 1 (j+1), g d) +
        (∑ d ∈ Finset.Ico 1 (Q-j), g d) := by
  let f := fun k : ℕ => g (Nat.dist j k)
  have hleft : (∑ k ∈ Finset.Ico 0 j, f k) =
      ∑ d ∈ Finset.Ico 1 (j+1), g d := by
    have h := Finset.sum_Ico_reflect g 0 (m:=j) (n:=j)
      (by omega)
    calc
      (∑ k ∈ Finset.Ico 0 j, f k) =
        ∑ k ∈ Finset.Ico 0 j, g (j-k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkj : k ≤ j := (Finset.mem_Ico.mp hk).2.le
          simp only [f]
          rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hkj]
      _ = _ := by
        have hi : j+1-j=1 := by omega
        simpa only [hi, Nat.sub_zero] using h
  have hright : (∑ k ∈ Finset.Ico (j+1) Q, f k) =
      ∑ d ∈ Finset.Ico 1 (Q-j), g d := by
    have hh : (∑ k ∈ Finset.Ico (j+1) Q, f k) =
        ∑ k ∈ Finset.Ico (j+1) Q, g (k-j) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hjk : j ≤ k := by
        have := (Finset.mem_Ico.mp hk).1
        omega
      simp only [f]
      exact congrArg g (Nat.dist_eq_sub_of_le hjk)
    rw [hh]
    have h := Finset.sum_Ico_add
      (fun k : ℕ => g (k-j)) 1 (Q-j) j
    have hQ : Q-j+j=Q := by omega
    have h1 :
        (∑ k ∈ Finset.Ico 1 (Q-j), g ((j+k)-j)) =
          ∑ k ∈ Finset.Ico (j+1) Q, g (k-j) := by
      simpa only [add_comm 1 j, hQ] using h
    calc
      (∑ k ∈ Finset.Ico (j+1) Q, g (k-j)) =
          ∑ k ∈ Finset.Ico 1 (Q-j), g ((j+k)-j) := h1.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        simp
  have hdiag : (∑ k ∈ Finset.Ico j (j+1), f k) = g 0 := by
    simp [f]
  have hsplit1 := Finset.sum_Ico_consecutive f
    (m:=0) (n:=j) (k:=Q) (by omega) (by omega)
  have hsplit2 := Finset.sum_Ico_consecutive f
    (m:=j) (n:=j+1) (k:=Q) (by omega) (by omega)
  have hparts : (∑ k ∈ Finset.Ico 0 Q, f k) =
      (∑ k ∈ Finset.Ico 0 j, f k) +
      (∑ k ∈ Finset.Ico j (j+1), f k) +
      (∑ k ∈ Finset.Ico (j+1) Q, f k) := by
    rw [← hsplit1, ← hsplit2]
    ring
  have hrange : (∑ k ∈ Finset.range Q, f k) =
      ∑ k ∈ Finset.Ico 0 Q, f k := by simp
  calc
    (∑ k ∈ Finset.range Q, g (Nat.dist j k)) =
        ∑ k ∈ Finset.Ico 0 Q, f k := hrange
    _ = _ := hparts
    _ = _ := by rw [hleft, hdiag, hright]; ring

theorem nat_distance_row_bound (g : ℕ → ℝ)
    (Q j : ℕ) (hj : j < Q) (P D : ℝ)
    (hzero : g 0 ≤ P)
    (hgnonneg : ∀ d ∈ Finset.Ico 1 Q, 0 ≤ g d)
    (hsum : (∑ d ∈ Finset.Ico 1 Q, g d) ≤ D) :
    (∑ k ∈ Finset.range Q, g (Nat.dist j k)) ≤ P+2*D := by
  rw [nat_distance_row_identity g Q j hj]
  have hsub1 : Finset.Ico 1 (j+1) ⊆ Finset.Ico 1 Q :=
    Finset.Ico_subset_Ico (le_refl _) (by omega)
  have hsub2 : Finset.Ico 1 (Q-j) ⊆ Finset.Ico 1 Q :=
    Finset.Ico_subset_Ico (le_refl _) (by omega)
  have hleft := Finset.sum_le_sum_of_subset_of_nonneg hsub1
    (by intro d hd hnot; exact hgnonneg d hd)
  have hright := Finset.sum_le_sum_of_subset_of_nonneg hsub2
    (by intro d hd hnot; exact hgnonneg d hd)
  linarith

end Green64SourceC6

end

/-! ## C6SymmetricKernel -/

section

namespace Green64SourceC6

/-- Exact complex conjugation on the source additive character. -/
theorem integerPhase_negTheta (theta : ℝ) (m : ℤ) :
    integerPhase (-theta) m = star (integerPhase theta m) := by
  unfold integerPhase
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Every translated source geometric kernel is even after taking norms. -/
theorem translated_kernel_norm_even (alpha : ℝ) (d M : ℤ) (P : ℕ) :
    ‖∑ m ∈ Finset.range P,
      integerPhase (alpha * (-(d:ℝ))) (M+(m:ℤ))‖ =
    ‖∑ m ∈ Finset.range P,
      integerPhase (alpha * (d:ℝ)) (M+(m:ℤ))‖ := by
  have hs :
      (∑ m ∈ Finset.range P,
         integerPhase (alpha*(-(d:ℝ))) (M+(m:ℤ))) =
      star (∑ m ∈ Finset.range P,
         integerPhase (alpha*(d:ℝ)) (M+(m:ℤ))) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro m hm
    convert integerPhase_negTheta (alpha*(d:ℝ)) (M+(m:ℤ)) using 1 <;> ring
  rw [hs, norm_star]

end Green64SourceC6

end

/-! ## C6KernelGram -/

section

namespace Green64SourceC6

theorem integerPhase_mul_conj (theta eta : ℝ) (m : ℤ) :
    integerPhase theta m * star (integerPhase eta m) =
      integerPhase (theta-eta) m := by
  rw [← integerPhase_negTheta eta m]
  unfold integerPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Phase depends on the distance of literal arbitrary shifted integer
indices, even for negative starting points. -/
theorem literal_gram_kernel_distance
    (alpha : ℝ) (M : ℤ) (P j k : ℕ) :
    ‖∑ m ∈ Finset.range P,
      integerPhase (alpha * (((j:ℤ)-(k:ℤ)):ℝ))
        (M+(m:ℤ))‖ =
    ‖∑ m ∈ Finset.range P,
      integerPhase (alpha * ((Nat.dist j k : ℕ):ℝ))
        (M+(m:ℤ))‖ := by
  rcases le_total j k with h | h
  · have hdist : Nat.dist j k = k-j :=
      Nat.dist_eq_sub_of_le h
    have hcast : ((j:ℤ)-(k:ℤ)) = -((k-j : ℕ):ℤ) := by
      omega
    have hreal : (j:ℝ)-(k:ℝ) = -((k-j:ℕ):ℝ) := by
      exact_mod_cast hcast
    simpa only [Int.cast_sub, Int.cast_natCast, hdist, hreal] using
      (translated_kernel_norm_even alpha ((k-j:ℕ):ℤ) M P)
  · have hdist : Nat.dist j k = j-k := by
      rw [Nat.dist_comm]
      exact Nat.dist_eq_sub_of_le h
    have hcast : ((j:ℤ)-(k:ℤ)) = ((j-k : ℕ):ℤ) := by omega
    have hreal : (j:ℝ)-(k:ℝ) = ((j-k:ℕ):ℝ) := by
      exact_mod_cast hcast
    simp only [Int.cast_sub, Int.cast_natCast, hdist, hreal]

end Green64SourceC6

end

/-! ## C6SourceRow -/

section

namespace Green64SourceC6

/-- The complete source quantitative Gram row, including the resonant
r=1 case. The only hypotheses are the actual coprime rational arc
and beta range; no coefficient hypotheses are introduced. -/
theorem source_gram_row_bound
    (a : ℤ) (r P Q : ℕ) (beta : ℝ) (M : ℤ)
    (hr : 0 < r)
    (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta| ≤ 1/((r:ℝ)^2))
    (j : ℕ) (hj : j < Q) :
    (∑ k ∈ Finset.range Q,
      ‖∑ m ∈ Finset.range P,
          integerPhase (((a:ℝ)/(r:ℝ)+beta)*
             (((Nat.dist j k : ℕ):ℝ))) (M+(m:ℤ))‖) ≤
      25 * ((P:ℝ) + (1+(Q:ℝ)/(r:ℝ)) *
        ((P:ℝ) + (r:ℝ)*Real.log (2*(r:ℝ)))) := by
  let alpha : ℝ := (a:ℝ)/(r:ℝ)+beta
  let g := fun d : ℕ =>
      ‖∑ m ∈ Finset.range P,
        integerPhase (alpha*(d:ℝ)) (M+(m:ℤ))‖
  let C : ℝ := (P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ))
  let D : ℝ := 12*(1+(Q:ℝ)/(r:ℝ))*C
  have h0 : g 0 ≤ (P:ℝ) := by
    simpa [g] using
      (translated_additive_kernel (alpha*(0:ℝ)) M P).1
  have hnonneg : ∀ d ∈ Finset.Ico 1 Q, 0 ≤ g d := by
    intro d hd
    exact norm_nonneg _
  by_cases hsmall : r=1
  · have hpoint : ∀ k ∈ Finset.range Q,
        g (Nat.dist j k) ≤ (P:ℝ) := by
      intro k hk
      exact (translated_additive_kernel
        (alpha * ((Nat.dist j k:ℕ):ℝ)) M P).1
    have hsum := Finset.sum_le_card_nsmul
      (Finset.range Q) (fun k => g (Nat.dist j k))
      (P:ℝ) hpoint
    rw [nsmul_eq_mul] at hsum
    simp only [Finset.card_range] at hsum
    have hP : 0 ≤ (P:ℝ) := by positivity
    have hQ : 0 ≤ (Q:ℝ) := by positivity
    have hlog : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num)
    have hbound : (Q:ℝ)*(P:ℝ) ≤
        25 * ((P:ℝ) + (1+(Q:ℝ)) *
          ((P:ℝ) + Real.log 2)) := by
      nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 1+(Q:ℝ)) hlog]
    have hconclusion := hsum.trans hbound
    simpa [g, C, D, alpha, hsmall] using hconclusion
  · have hr2 : 2 ≤ r := by omega
    have hD : (∑ d ∈ Finset.Ico 1 Q, g d) ≤ D := by
      exact source_global_positive_difference_sum a r Q P beta M
        hr2 hcop hbeta
    have hrow := nat_distance_row_bound g Q j hj (P:ℝ) D
      h0 hnonneg hD
    have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
    have hlog : 0 ≤ Real.log (2*(r:ℝ)) := by
      apply Real.log_nonneg
      have hr2R : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr2
      nlinarith
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    have hfactor : 0 ≤ 1+(Q:ℝ)/(r:ℝ) := by positivity
    have hterm : 0 ≤ (1+(Q:ℝ)/(r:ℝ))*C :=
      mul_nonneg hfactor hC
    have hupper :
      (P:ℝ) + 2*D ≤
      25*((P:ℝ)+(1+(Q:ℝ)/(r:ℝ))*C) := by
      dsimp [D]
      nlinarith [show (0:ℝ) ≤ (P:ℝ) by positivity, hterm]
    exact (by simpa only [g,C,D] using hrow.trans hupper)

end Green64SourceC6

end

/-! ## C6ExactBilinear -/

section

namespace Green64SourceC6

/-- Complete source integer C6 bilinear minor-arc estimate in the
original squared L² form. A,B are unrestricted complex coefficient
functions, P,Q arbitrary lengths, M,N arbitrary integer translations.
There are no additional coefficient or distribution assumptions. -/
theorem source_integer_bilinear_minor_arc_sq
    (a : ℤ) (r P Q : ℕ) (beta : ℝ) (M N : ℤ)
    (A B : ℤ → ℂ)
    (hr : 0 < r)
    (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta| ≤ 1/((r:ℝ)^2)) :
    ‖∑ i ∈ Finset.range P,
        A (M+(i:ℤ)) *
        (∑ j ∈ Finset.range Q,
          B (N+(j:ℤ)) *
          integerPhase
            (((a:ℝ)/(r:ℝ)+beta) * ((N+(j:ℤ)):ℝ))
            (M+(i:ℤ)))‖^2 ≤
      (∑ i ∈ Finset.range P, ‖A (M+(i:ℤ))‖^2) *
      (25*((P:ℝ) + (1+(Q:ℝ)/(r:ℝ)) *
        ((P:ℝ) + (r:ℝ)*Real.log (2*(r:ℝ)))) *
      (∑ j ∈ Finset.range Q, ‖B (N+(j:ℤ))‖^2)) := by
  let alpha : ℝ := (a:ℝ)/(r:ℝ)+beta
  let E := fun i j : ℕ =>
    integerPhase (alpha * ((N+(j:ℤ)):ℝ)) (M+(i:ℤ))
  let K := fun j k : ℕ =>
    ‖∑ i ∈ Finset.range P,
      integerPhase (alpha *((Nat.dist j k:ℕ):ℝ)) (M+(i:ℤ))‖
  let R : ℝ := 25*((P:ℝ)+(1+(Q:ℝ)/(r:ℝ)) *
    ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ))))
  have hK : ∀ j ∈ Finset.range Q, ∀ k ∈ Finset.range Q,
      0 ≤ K j k := by
    intro j hj k hk
    exact norm_nonneg _
  have hsym : ∀ j ∈ Finset.range Q, ∀ k ∈ Finset.range Q,
      K j k = K k j := by
    intro j hj k hk
    dsimp [K]
    rw [Nat.dist_comm]
  have hphase (i j k : ℕ) :
      E i j * star (E i k) =
      integerPhase
        (alpha * (((j:ℤ)-(k:ℤ)):ℝ))
        (M+(i:ℤ)) := by
    calc
      E i j * star (E i k) =
          integerPhase
            (alpha*((N+(j:ℤ)):ℝ) - alpha*((N+(k:ℤ)):ℝ))
            (M+(i:ℤ)) :=
              integerPhase_mul_conj _ _ _
      _ = _ := by
        congr 1
        push_cast
        ring
  have hdom : ∀ j ∈ Finset.range Q, ∀ k ∈ Finset.range Q,
      ‖∑ i ∈ Finset.range P, E i j * star (E i k)‖ ≤
        K j k := by
    intro j hj k hk
    have hsum :
        (∑ i ∈ Finset.range P, E i j * star (E i k)) =
        ∑ i ∈ Finset.range P,
          integerPhase
            (alpha * (((j:ℤ)-(k:ℤ)):ℝ)) (M+(i:ℤ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hphase i j k
    rw [hsum]
    exact le_of_eq (literal_gram_kernel_distance alpha M P j k)
  have hrow : ∀ j ∈ Finset.range Q,
      (∑ k ∈ Finset.range Q, K j k) ≤ R := by
    intro j hj
    exact source_gram_row_bound a r P Q beta M hr hcop hbeta j
      (Finset.mem_range.mp hj)
  have hh := bilinear_from_gram_bound
    (Finset.range P) (Finset.range Q)
    (fun i => A (M+(i:ℤ))) (fun j => B (N+(j:ℤ)))
    E K R hK hsym hdom hrow
  simpa only [E, K, R, alpha] using hh

end Green64SourceC6

end

/-! ## C6ExactBilinearNorm -/

section

namespace Green64SourceC6

/-- The literal source C6 inequality with constant 5,
unrestricted complex coefficients and arbitrary translated integer intervals.
No sieve, discrepancy or Type II hypothesis is present. -/
theorem source_integer_bilinear_minor_arc
    (a : ℤ) (r P Q : ℕ) (beta : ℝ) (M N : ℤ)
    (A B : ℤ → ℂ)
    (hr : 0 < r)
    (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta| ≤ 1/((r:ℝ)^2)) :
    ‖∑ i ∈ Finset.range P,
        A (M+(i:ℤ)) *
        (∑ j ∈ Finset.range Q,
          B (N+(j:ℤ)) *
          integerPhase
            (((a:ℝ)/(r:ℝ)+beta) * ((N+(j:ℤ)):ℝ))
            (M+(i:ℤ)))‖ ≤
      5 * Real.sqrt (∑ i ∈ Finset.range P,
          ‖A (M+(i:ℤ))‖^2) *
        Real.sqrt (∑ j ∈ Finset.range Q,
          ‖B (N+(j:ℤ))‖^2) *
        Real.sqrt ((P:ℝ) + (1+(Q:ℝ)/(r:ℝ)) *
          ((P:ℝ) + (r:ℝ)*Real.log (2*(r:ℝ)))) := by
  let S := ∑ i ∈ Finset.range P,
        A (M+(i:ℤ)) *
        (∑ j ∈ Finset.range Q,
          B (N+(j:ℤ)) *
          integerPhase
            (((a:ℝ)/(r:ℝ)+beta) * ((N+(j:ℤ)):ℝ))
            (M+(i:ℤ)))
  let U : ℝ := ∑ i ∈ Finset.range P, ‖A (M+(i:ℤ))‖^2
  let V : ℝ := ∑ j ∈ Finset.range Q, ‖B (N+(j:ℤ))‖^2
  let T : ℝ := (P:ℝ)+(1+(Q:ℝ)/(r:ℝ)) *
    ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ)))
  have hu : 0 ≤ U := by
    dsimp [U]
    apply Finset.sum_nonneg
    intro i hi
    positivity
  have hv : 0 ≤ V := by
    dsimp [V]
    apply Finset.sum_nonneg
    intro j hj
    positivity
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hlog : 0 ≤ Real.log (2*(r:ℝ)) := by
    apply Real.log_nonneg
    have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    nlinarith
  have ht : 0 ≤ T := by
    dsimp [T]
    positivity
  have hs : ‖S‖^2 ≤ U*(25*T*V) :=
    source_integer_bilinear_minor_arc_sq a r P Q beta M N A B
      hr hcop hbeta
  let Z : ℝ := 5 * Real.sqrt U * Real.sqrt V * Real.sqrt T
  have hz : 0 ≤ Z := by dsimp [Z]; positivity
  have hsq : Z^2 = U*(25*T*V) := by
    dsimp [Z]
    calc
      (5 * Real.sqrt U * Real.sqrt V * Real.sqrt T)^2 =
          25 * (Real.sqrt U)^2 * (Real.sqrt V)^2 * (Real.sqrt T)^2 := by ring
      _ = U*(25*T*V) := by
        rw [Real.sq_sqrt hu, Real.sq_sqrt hv, Real.sq_sqrt ht]
        ring
  have hn : ‖S‖ ≤ Z := by
    have hn0 : 0 ≤ ‖S‖ := norm_nonneg _
    nlinarith
  exact hn

end Green64SourceC6

end

/-! ## SourceLinearCollarCompactGeometry -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 500000

/-- For TRUE original physical support n in [Y/A,A Y], the literal
linear collar K((n-v)/H) vanishes outside V=[Y/(2A),2AY].
This is the required support input for full-line Plancherel, not a
new energy/saving premise. -/
theorem source_linear_collar_true_window_support434
    (K : ℝ → ℂ) (n v Y A H δ : ℝ)
    (hA : 1 ≤ A) (hY : 0 < Y) (hH : 0 < H)
    (hHcap : H ≤ Y/(8*A))
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hSupportK : ∀ z, K z ≠ 0 → |z| ≤ δ)
    (hnLow : Y/A ≤ n) (hnHi : n ≤ A*Y)
    (hv : v ∉ Set.Icc (Y/(2*A)) (2*A*Y)) :
    K ((n-v)/H) = 0 := by
  by_contra hNonzero
  have hK := hSupportK ((n-v)/H) hNonzero
  rw [abs_div, abs_of_pos hH] at hK
  have hNear : |n-v| ≤ δ*H := (div_le_iff₀ hH).mp hK
  have hδH : δ*H ≤ H := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hδ1 hH.le
  have hAH : 0 < A := by linarith
  have h2A : 0 < 2*A := by positivity
  have h8A : 0 < 8*A := by positivity
  have hHLow : H ≤ Y/(2*A) := by
    have hp : 0 ≤ Y/(8*A) := by positivity
    have he : Y/(2*A)=4*(Y/(8*A)) := by
      field_simp
      ring
    linarith [hHcap]
  have hY8 : Y/(8*A) ≤ Y := by
    apply (div_le_iff₀ h8A).mpr
    nlinarith
  have hYAY : Y ≤ A*Y := by nlinarith
  have hHHigh : H ≤ A*Y := hHcap.trans (hY8.trans hYAY)
  obtain ⟨hNearLo,hNearHi⟩ := abs_le.mp (hNear.trans hδH)
  have hDivide : Y/A=2*(Y/(2*A)) := by
    field_simp
  have hVLow : Y/(2*A) ≤ v := by linarith
  have hVHi : v ≤ 2*A*Y := by linarith
  exact hv (Set.mem_Icc.mpr ⟨hVLow,hVHi⟩)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLinearCollarSchwartz -/

section

open MeasureTheory
open scoped SchwartzMap BigOperators FourierTransform
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 700000

/-- Genuine ordinary collar term is Schwartz, including translation,
reflection and the exact scale H. No L2 assumption is introduced. -/
theorem source_linear_term_schwartz_exists434
    (K : 𝓢(ℝ,ℂ)) (n H : ℝ) (hH : 0 < H) :
    ∃ Q : 𝓢(ℝ,ℂ), (Q : ℝ → ℂ) =
      (fun v : ℝ => K ((n-v)/H)) := by
  let g : ℝ → ℝ := fun v => (n-v)/H
  have ht : g.HasTemperateGrowth := by
    dsimp [g]
    simp only [div_eq_mul_inv]
    fun_prop
  have hproper : ∃ (k : ℕ) (C : ℝ),
      ∀ v : ℝ, ‖v‖ ≤ C*(1+‖g v‖)^k := by
    refine ⟨1, |n|+H, ?_⟩
    intro v
    have hv : v = n-H*g v := by
      dsimp [g]
      field_simp
      ring
    have hb : |v| ≤ |n|+H*|g v| := by
      calc
        |v| = |n-H*g v| := congrArg abs hv
        _ ≤ |n|+|H*g v| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_of_pos hH]
    simp only [Real.norm_eq_abs, pow_one]
    nlinarith [abs_nonneg n, abs_nonneg (g v)]
  refine ⟨SchwartzMap.compCLM ℂ ht hproper K, ?_⟩
  rfl

/-- The finite physical linear collar itself is Schwartz; this proves
all required L1 and L2 regularity without a source-energy premise. -/
theorem source_linear_finite_schwartz_exists434
    (K : 𝓢(ℝ,ℂ)) (F : Finset ℕ) (a : ℕ → ℂ)
    (H : ℝ) (hH : 0 < H) :
    ∃ Q : 𝓢(ℝ,ℂ), (Q : ℝ → ℂ) =
      (fun v : ℝ => ∑ n ∈ F, a n*K (((n:ℝ)-v)/H)) := by
  classical
  choose q hq using (fun n : ℕ =>
    source_linear_term_schwartz_exists434 K (n:ℝ) H hH)
  refine ⟨∑ n ∈ F, a n • q n, ?_⟩
  funext v
  simp only [SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [show q n v = K (((n:ℝ)-v)/H) from congrFun (hq n) v]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCompactBumpBand -/

section

open MeasureTheory
open scoped SchwartzMap FourierTransform Topology
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 900000

/-- Continuity gives a fixed positive Fourier neighborhood for the
concrete smooth compact bump, independent of all arithmetic data. -/
theorem source_compact_bump_local_band434 :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ s : ℝ,
      |s| < ε → c ≤ ‖(𝓕 (sourceCompactBumpSchwartz434 : ℝ → ℂ)) s‖ := by
  let f : ℝ → ℝ := fun s =>
    ‖(𝓕 (sourceCompactBumpSchwartz434 : ℝ → ℂ)) s‖
  have hf : Continuous f := by
    simpa only [f, SchwartzMap.fourier_coe] using
      (𝓕 sourceCompactBumpSchwartz434 : 𝓢(ℝ,ℂ)).continuous.norm
  have hpos : 0 < f 0 := source_compact_bump_fourier_zero_pos434
  have he : ∀ᶠ s in 𝓝 (0:ℝ), f 0 / 2 < f s :=
    hf.continuousAt.eventually (lt_mem_nhds (by linarith : f 0 / 2 < f 0))
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ε, f 0 / 2, hε, by positivity, ?_⟩
  intro s hs
  exact (he (by simpa [Real.dist_eq] using hs)).le

/-- One actual C-infinity compact kernel has a uniformly positive
Fourier transform norm on the entire required [-1,1] band. -/
theorem source_compact_bump_full_band_exists434 :
    ∃ (K : 𝓢(ℝ,ℂ)) (δ c : ℝ),
      0 < δ ∧ δ ≤ 1 ∧ 0 < c ∧
      (∀ x : ℝ, K x ≠ 0 → |x| ≤ δ) ∧
      (∀ s : ℝ, |s| ≤ 1 → c ≤ ‖(𝓕 (K : ℝ → ℂ)) s‖) := by
  obtain ⟨ε,c,hε,hc,hlocal⟩ := source_compact_bump_local_band434
  let δ : ℝ := min 1 (ε/2)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
  obtain ⟨K,hK⟩ := source_linear_term_schwartz_exists434
    sourceCompactBumpSchwartz434 0 δ hδ
  have hK' : (K : ℝ → ℂ) =
      fun x : ℝ => sourceCompactBumpSchwartz434 ((-x)/δ) := by
    simpa only [zero_sub] using hK
  refine ⟨K,δ,δ*c,hδ,hδ1,mul_pos hδ hc,?_,?_⟩
  · intro x hx
    have hb : |(-x)/δ| ≤ 1 := source_compact_bump_support434 _
      (by simpa only [hK'] using hx)
    rw [abs_div,abs_neg,abs_of_pos hδ] at hb
    exact (div_le_iff₀ hδ).mp hb |>.trans_eq (one_mul δ)
  · intro s hs
    rw [hK',source_linear_collar_fourier_dilation434 _ δ hδ]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
    apply mul_le_mul_of_nonneg_left _ hδ.le
    apply hlocal
    rw [abs_mul,abs_neg,abs_of_pos hδ]
    exact (mul_le_of_le_one_right hδ.le hs).trans_lt hδε
end Green64Analytic.CorrelationSquare

end

