module

public import Green64.Library.ChenTheorem.Lemma6.Core
public import Green64.Library.Weights.Part032
public import Green64.Library.Sieve.Foundation.Lemma9.Part005
public import Mathlib.Algebra.BigOperators.Module
public import Green64.Library.Weights.Part012
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Analysis / Estimates / Part005

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourcePrimePowerAbsorption -/

section

open Filter Real
open scoped Classical

namespace Green64Analytic.SourceSW

/-- The genuine prime-power contribution is negligible at every fixed
inverse logarithmic scale; no Siegel-Walfisz input is used. -/
theorem eventually_primePowerError_le_logSaving (K : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) ≤
        (x : ℝ) / Real.log (x : ℝ) ^ K := by
  have hA := Chen.eventually_const_mul_log_pow_le_rpow
    2 (K + 1) (δ := (1 : ℝ) / 2) (by norm_num)
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 3, hA,
    hlogT.eventually (eventually_ge_atTop 1)] with x hx hA hlog
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hsqrt : 2 * Real.log (x : ℝ) ^ (K + 1) ≤ Real.sqrt (x : ℝ) := by
    simpa only [Real.sqrt_eq_rpow] using hA
  have hprod := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg (x : ℝ))
  apply (le_div_iff₀ (pow_pos hlogpos K)).mpr
  calc
    (2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ)) *
        Real.log (x : ℝ) ^ K =
      (2 * Real.log (x : ℝ) ^ (K + 1)) * Real.sqrt (x : ℝ) := by
        rw [pow_succ]
        ring
    _ ≤ Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) := hprod
    _ = (x : ℝ) := by nlinarith [Real.sq_sqrt hx0]
end Green64Analytic.SourceSW

end

/-! ## SourceNativeThetaLogSaving -/

section

open Filter Real
open scoped Classical

namespace Green64Analytic.SourceSW

/-- Uniform, unconditional prime-log-weight cancellation at polylogarithmic
primitive conductors, with arbitrary fixed log saving. -/
theorem norm_twistedTheta_smallConductor_unconditional
    (K R : ℕ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        2 ≤ q → (q : ℝ) ≤ Real.log (x : ℝ) ^ R →
          χ.IsPrimitive →
          ‖twistedTheta x χ‖ ≤
            C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
  obtain ⟨C, hC, hPsi⟩ := norm_twistedPsi_smallConductor_unconditional K R hR
  have hPow := eventually_primePowerError_le_logSaving K
  refine ⟨C + 1, by linarith, ?_⟩
  filter_upwards [hPsi, hPow, eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop 0)] with x hPsi hPow hx hlog
  intro q _ χ hq hqR hχ
  have hb := hPsi q χ hq hqR hχ
  have hθ := norm_twistedTheta_le_twistedPsi_add_primePowerError
    (by omega : 1 ≤ x) χ
  calc
    ‖twistedTheta x χ‖ ≤
        ‖Chen.BombieriVinogradov.twistedPsi x χ‖ +
          2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) := hθ
    _ ≤ C * (x : ℝ) / Real.log (x : ℝ) ^ K +
          (x : ℝ) / Real.log (x : ℝ) ^ K := add_le_add hb hPow
    _ = (C + 1) * (x : ℝ) / Real.log (x : ℝ) ^ K := by ring
end Green64Analytic.SourceSW

end

/-! ## SourceAbelMonotone -/

section

open Filter Real
open scoped Classical BigOperators

namespace Green64Analytic.SourceSW

/-- Discrete Abel summation with nonnegative nonincreasing real weights.
No analytic convergence or Siegel--Walfisz input is used here. -/
theorem norm_sum_range_antitone_weight_le
    (w : ℕ → ℝ) (g : ℕ → ℂ) (N : ℕ) (H : ℝ)
    (hH : 0 ≤ H)
    (hwpos : ∀ i, 0 ≤ w i)
    (hwmon : ∀ i, w (i+1) ≤ w i)
    (hg : ∀ k, k ≤ N → ‖∑ i ∈ Finset.range k, g i‖ ≤ H) :
    ‖∑ i ∈ Finset.range N, (w i : ℂ) * g i‖ ≤ w 0 * H := by
  let f : ℕ → ℂ := fun i => (w i : ℂ)
  have hparts := Finset.sum_range_by_parts f g N
  simp only [smul_eq_mul] at hparts
  have htel (n : ℕ) :
      (∑ i ∈ Finset.range n, (w i - w (i+1))) = w 0 - w n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  have hvar (n : ℕ) :
      ‖f n‖ + ∑ i ∈ Finset.range n, ‖f (i+1) - f i‖ = w 0 := by
    change ‖(w n : ℂ)‖ +
      ∑ i ∈ Finset.range n, ‖(w (i+1) : ℂ) - (w i : ℂ)‖ = w 0
    simp only [Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_sub]
    rw [abs_of_nonneg (hwpos n)]
    have hsum :
      (∑ i ∈ Finset.range n, |w (i+1) - w i|) =
        ∑ i ∈ Finset.range n, (w i - w (i+1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_of_nonpos (sub_nonpos.mpr (hwmon i))]
      ring
    rw [hsum, htel]
    ring
  rw [hparts]
  calc
    ‖f (N-1) * (∑ i ∈ Finset.range N, g i) -
      ∑ i ∈ Finset.range (N-1),
        (f (i+1) - f i) * (∑ j ∈ Finset.range (i+1), g j)‖ ≤
      ‖f (N-1)‖ * H +
        ∑ i ∈ Finset.range (N-1), ‖f (i+1) - f i‖ * H := by
        apply (norm_sub_le _ _).trans
        apply add_le_add
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hg N (le_refl _)) (norm_nonneg _)
        · apply (norm_sum_le _ _).trans
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_mul]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply hg (i+1)
          have := Finset.mem_range.mp hi
          omega
    _ = H * (‖f (N-1)‖ +
        ∑ i ∈ Finset.range (N-1), ‖f (i+1) - f i‖) := by
        rw [← Finset.sum_mul]
        ring
    _ = w 0 * H := by rw [hvar]; ring
end Green64Analytic.SourceSW

end

/-! ## SourceAbelIntervals -/

section

open Filter Real
open scoped Classical BigOperators

namespace Green64Analytic.SourceSW

/-- Exact finite reindexing, including the case of an empty interval. -/
theorem sum_Ioc_as_range (M N : ℕ) (g : ℕ → ℂ) :
    (∑ p ∈ Finset.Ioc M (M+N), g p) =
      ∑ i ∈ Finset.range N, g (M+i+1) := by
  symm
  apply Finset.sum_bij (fun i _ => M+i+1)
  · intro i hi
    apply Finset.mem_Ioc.mpr
    have := Finset.mem_range.mp hi
    omega
  · intro i hi j hj he
    omega
  · intro p hp
    have hh := Finset.mem_Ioc.mp hp
    refine ⟨p-M-1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    rfl

/-- The true prime logarithmic weight on `(a,b]` is a difference of
the previously kernel-checked twisted Chebyshev theta prefixes. -/
theorem theta_Ioc_eq_twistedTheta_sub {q a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.Ioc a b,
      if n.Prime then (Real.log n : ℂ) * χ n else 0) =
        twistedTheta b χ - twistedTheta a χ := by
  let g : ℕ → ℂ := fun n =>
    if n.Prime then (Real.log n : ℂ) * χ n else 0
  have hunion : Finset.Icc 1 a ∪ Finset.Ioc a b = Finset.Icc 1 b := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 a) (Finset.Ioc a b) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    have hna := Finset.mem_Icc.mp hn
    have hnb := Finset.mem_Ioc.mp hm
    omega
  have hsum := Finset.sum_union hdisj (f := g)
  have hsplit :
      (∑ n ∈ Finset.Icc 1 b, g n) =
        (∑ n ∈ Finset.Icc 1 a, g n) +
          (∑ n ∈ Finset.Ioc a b, g n) := by
    rw [← hunion, hsum]
  dsimp only [twistedTheta, g]
  rw [hsplit]
  ring

/-- The raw prime-character sum is Abel-weighted theta on its genuine
finite interval, with no character hypotheses. -/
theorem raw_prime_Ioc_eq_weightedTheta {q a b : ℕ}
    (hab : a ≤ b) (χ : DirichletCharacter ℂ q) :
    (∑ p ∈ Finset.Ioc a b, if p.Prime then χ p else 0) =
      ∑ i ∈ Finset.range (b-a),
        ((Real.log (a+i+1 : ℕ))⁻¹ : ℂ) *
          (if (a+i+1).Prime then
            (Real.log (a+i+1 : ℕ) : ℂ) * χ (a+i+1) else 0) := by
  have hb : b = a + (b-a) := by omega
  conv_lhs => rw [hb, sum_Ioc_as_range]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hp : (a+i+1).Prime
  · simp only [if_pos hp]
    have hp2 : 1 < (a+i+1 : ℕ) := hp.one_lt
    have hlog : Real.log ((a+i+1 : ℕ) : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hp2))
    have hcast : (Real.log (a+i+1 : ℕ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hlog
    rw [← mul_assoc, inv_mul_cancel₀ hcast, one_mul]
    simp only [Nat.cast_add, Nat.cast_one]
  · simp [hp]
end Green64Analytic.SourceSW

end

/-! ## SourceAbelPrimeBound -/

section

open Filter Real
open scoped Classical BigOperators

namespace Green64Analytic.SourceSW

/-- Literal unweighted prime-character interval estimate from a uniform
bound on the true logarithmically weighted Chebyshev prefixes. -/
theorem norm_raw_prime_Ioc_le_of_theta_prefix
    {q a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b)
    (χ : DirichletCharacter ℂ q) (H : ℝ) (hH : 0 ≤ H)
    (hθ : ∀ n : ℕ, a ≤ n → n ≤ b → ‖twistedTheta n χ‖ ≤ H) :
    ‖∑ p ∈ Finset.Ioc a b, if p.Prime then χ p else 0‖ ≤
      2 * H / Real.log (a+1 : ℕ) := by
  let w : ℕ → ℝ := fun i => (Real.log (a+i+1 : ℕ))⁻¹
  let g : ℕ → ℂ := fun i =>
    if (a+i+1).Prime then (Real.log (a+i+1 : ℕ) : ℂ) * χ (a+i+1) else 0
  have hlogpos (i : ℕ) : 0 < Real.log (a+i+1 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a+i+1 by omega))
  have hwpos : ∀ i, 0 ≤ w i := by
    intro i
    exact inv_nonneg.mpr (hlogpos i).le
  have hwmon : ∀ i, w (i+1) ≤ w i := by
    intro i
    have hlogle : Real.log (a+i+1 : ℕ) ≤
        Real.log (a+(i+1)+1 : ℕ) := by
      apply Real.log_le_log (by exact_mod_cast (show 0 < a+i+1 by omega))
      exact_mod_cast (show a+i+1 ≤ a+(i+1)+1 by omega)
    change (Real.log (a+(i+1)+1 : ℕ))⁻¹ ≤
      (Real.log (a+i+1 : ℕ))⁻¹
    simpa only [one_div] using (one_div_le_one_div_of_le (hlogpos i) hlogle)
  have hgpref : ∀ k, k ≤ b-a →
      ‖∑ i ∈ Finset.range k, g i‖ ≤ 2*H := by
    intro k hk
    have hsk : (∑ i ∈ Finset.range k, g i) =
        twistedTheta (a+k) χ - twistedTheta a χ := by
      calc
        (∑ i ∈ Finset.range k, g i) =
          ∑ n ∈ Finset.Ioc a (a+k),
            if n.Prime then (Real.log n : ℂ) * χ n else 0 := by
              simpa only [g, Nat.cast_add, Nat.cast_one] using (sum_Ioc_as_range a k
                (fun n => if n.Prime then (Real.log n : ℂ)*χ n else 0)).symm
        _ = _ := theta_Ioc_eq_twistedTheta_sub (by omega) (by omega) χ
    rw [hsk]
    have haθ := hθ a (le_refl _) hab
    have hbθ := hθ (a+k) (by omega) (by omega)
    exact (norm_sub_le _ _).trans (by linarith)
  have hraw := raw_prime_Ioc_eq_weightedTheta hab χ
  rw [hraw]
  have hbound := norm_sum_range_antitone_weight_le
    w g (b-a) (2*H) (by positivity) hwpos hwmon hgpref
  change ‖∑ i ∈ Finset.range (b-a), (w i : ℂ)*g i‖ ≤ _ at hbound
  calc
    ‖∑ i ∈ Finset.range (b-a),
      ((Real.log (a+i+1 : ℕ))⁻¹ : ℂ) *
        (if (a+i+1).Prime then
          (Real.log (a+i+1 : ℕ) : ℂ) * χ (a+i+1) else 0)‖ =
      ‖∑ i ∈ Finset.range (b-a), (w i : ℂ)*g i‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [w, g]
        rw [Complex.ofReal_inv]
    _ ≤ w 0 * (2*H) := hbound
    _ = 2 * H / Real.log (a+1 : ℕ) := by
        dsimp only [w]
        simp only [Nat.add_zero]
        rw [div_eq_mul_inv]
        ring
end Green64Analytic.SourceSW

end

/-! ## SourceSWScaleGeometry -/

section

open Filter Real
open scoped Classical
namespace Green64Analytic.SourceSW

/-- A uniform exponent comparison for real scales and natural endpoints.
The harmless squaring absorbs the shift of at most one integer. -/
theorem log_real_scale_le_log_nat_sq
    (y : ℝ) (n : ℕ) (hy : 0 < y)
    (hn : Real.exp 3 ≤ (n : ℝ)) (hyn : y ≤ (n : ℝ)+1) :
    Real.log y ≤ Real.log (n : ℝ) ^ 2 := by
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos 3) hn
  have hlogn : 3 ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 3) hn
    simpa only [Real.log_exp] using h
  have hn4 : (4 : ℝ) ≤ (n : ℝ) :=
    (by linarith [Real.add_one_le_exp (3:ℝ)] :
      (4:ℝ) ≤ Real.exp 3).trans hn
  have hysq : y ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n:ℝ)-2)]
  have hlog := Real.log_le_log hy hysq
  rw [Real.log_pow] at hlog
  have hquad : 2 * Real.log (n:ℝ) ≤ Real.log (n:ℝ) ^ 2 := by
    have hmul := mul_nonneg
      (show 0 ≤ Real.log (n:ℝ) by linarith)
      (show 0 ≤ Real.log (n:ℝ) - 2 by linarith)
    nlinarith
  exact hlog.trans hquad

/-- Uniform comparison of every integral logarithmic conductor power. -/
theorem log_real_scale_nat_pow_le
    (y : ℝ) (n r : ℕ) (hy : 0 ≤ Real.log y)
    (hlog : Real.log y ≤ Real.log (n : ℝ) ^ 2) :
    Real.log y ^ r ≤ Real.log (n : ℝ) ^ (2*r) := by
  have h := pow_le_pow_left₀ hy hlog r
  simpa only [pow_mul] using h
end Green64Analytic.SourceSW

end

/-! ## SourceSWNaturalPowers -/

section

open Filter Real
open scoped Classical BigOperators
namespace Green64Analytic.SourceSW

/-- Uniform Siegel--Walfisz prime intervals at a real scale, initially for
natural logarithmic conductor and saving exponents. -/
theorem raw_prime_real_scale_natural_log_saving
    (K R : ℕ) (hR : 1 ≤ R) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ y : ℝ in atTop,
      ∀ (f a b : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f),
        χ.IsPrimitive → 2 ≤ f → (f : ℝ) ≤ Real.log y ^ R →
        y ≤ (a:ℝ)+1 → a ≤ b → (b:ℝ) ≤ 2*y →
        ‖∑ p ∈ Finset.Ioc a b, if p.Prime then χ p else 0‖ ≤
          D * y / Real.log y ^ (K+1) := by
  obtain ⟨C, hC, hθ⟩ :=
    norm_twistedTheta_smallConductor_unconditional (2*K) (2*R) (by omega)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hθ
  refine ⟨4*C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop
      (max ((N:ℝ)+2) (Real.exp 3 + 2))] with y hy
  have hylarge : Real.exp 3 + 2 ≤ y := (le_max_right _ _).trans hy
  have hNlarge : (N:ℝ)+2 ≤ y := (le_max_left _ _).trans hy
  have hypos : 0 < y := by linarith [Real.exp_pos (3:ℝ)]
  have hlogy3 : 3 ≤ Real.log y := by
    have hh : Real.exp 3 ≤ y := by linarith
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 3) hh
  have hlogypos : 0 < Real.log y := by linarith
  intro f a b inst χ hprim hf2 hfR hay hab hby
  have haexp : Real.exp 3 ≤ (a:ℝ) := by linarith
  have ha2 : 2 ≤ a := by
    have hh : (2:ℝ) ≤ a := by
      linarith [Real.add_one_le_exp (3:ℝ)]
    exact_mod_cast hh
  let H : ℝ := 2*C*y / Real.log y ^ K
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hθbox : ∀ n : ℕ, a ≤ n → n ≤ b →
      ‖twistedTheta n χ‖ ≤ H := by
    intro n han hnb
    have hnexp : Real.exp 3 ≤ (n:ℝ) := haexp.trans (by exact_mod_cast han)
    have hyn : y ≤ (n:ℝ)+1 := hay.trans (by exact_mod_cast (Nat.add_le_add_right han 1))
    have hnscale := log_real_scale_le_log_nat_sq y n hypos hnexp hyn
    have hpowR := log_real_scale_nat_pow_le y n R
      (by linarith : 0 ≤ Real.log y) hnscale
    have hpowK := log_real_scale_nat_pow_le y n K
      (by linarith : 0 ≤ Real.log y) hnscale
    have hqR : (f:ℝ) ≤ Real.log (n:ℝ) ^ (2*R) := hfR.trans hpowR
    have hNn : N ≤ n := by
      have hh : (N:ℝ) ≤ (n:ℝ) := by linarith
      exact_mod_cast hh
    have hθn := hN n hNn f χ hf2 hqR hprim
    have hnle : (n:ℝ) ≤ 2*y := (by exact_mod_cast hnb : (n:ℝ) ≤ (b:ℝ)).trans hby
    have hden : 0 < Real.log y ^ K := pow_pos hlogypos K
    have hnum : C*(n:ℝ) ≤ C*(2*y) := mul_le_mul_of_nonneg_left hnle hC.le
    change ‖twistedTheta n χ‖ ≤ 2*C*y / Real.log y ^ K
    calc
      ‖twistedTheta n χ‖ ≤ C*(n:ℝ) / Real.log (n:ℝ) ^ (2*K) := hθn
      _ ≤ C*(n:ℝ) / Real.log y ^ K :=
        div_le_div_of_nonneg_left
          (mul_nonneg hC.le (Nat.cast_nonneg n)) hden hpowK
      _ ≤ C*(2*y) / Real.log y ^ K :=
        div_le_div_of_nonneg_right hnum hden.le
      _ = 2*C*y / Real.log y ^ K := by ring
  have hraw := norm_raw_prime_Ioc_le_of_theta_prefix ha2 hab χ H hH hθbox
  have hlogay : Real.log y ≤ Real.log (a+1 : ℕ) := by
    apply Real.log_le_log hypos
    simpa only [Nat.cast_add, Nat.cast_one] using hay
  have hweak : 2*H / Real.log (a+1 : ℕ) ≤ 2*H / Real.log y :=
    div_le_div_of_nonneg_left (by positivity) hlogypos hlogay
  calc
    ‖∑ p ∈ Finset.Ioc a b, if p.Prime then χ p else 0‖ ≤
      2*H / Real.log (a+1 : ℕ) := hraw
    _ ≤ 2*H / Real.log y := hweak
    _ = (4*C)*y / Real.log y ^ (K+1) := by
      dsimp only [H]
      rw [pow_succ]
      field_simp [ne_of_gt hlogypos, ne_of_gt (pow_pos hlogypos K)]
      ring
end Green64Analytic.SourceSW

end

/-! ## SourceSWRealQuantifiers -/

section

open Filter Real
open scoped Classical BigOperators
namespace Green64Analytic.SourceSW

/-- The EXACT quantifier body of the source `SourcePrimeSiegelWalfisz`,
with no foundational SW hypothesis and the original real endpoints. -/
theorem sourcePrimeSiegelWalfisz_exact_body :
    ∀ C A : ℝ, 0 < C → 0 < A →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ y : ℝ in atTop,
      ∀ (f a b : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f),
        χ.IsPrimitive → χ ≠ 1 → (f:ℝ) ≤ (Real.log y)^C →
        y ≤ (a:ℝ)+1 → a ≤ b → (b:ℝ) ≤ 2*y →
        ‖∑ p ∈ Finset.Ioc a b, if p.Prime then χ p else 0‖ ≤
          K*y*(Real.log y)^(-A) := by
  intro C₀ A₀ hC₀ hA₀
  let R : ℕ := ⌈C₀⌉₊ + 1
  let K : ℕ := ⌈A₀⌉₊ + 1
  have hR : 1 ≤ R := by dsimp only [R]; omega
  have hCR : C₀ ≤ (R:ℝ) := by
    dsimp only [R]
    have hh := Nat.le_ceil C₀
    push_cast
    linarith
  have hAK : A₀ ≤ (K+1:ℝ) := by
    dsimp only [K]
    have hh := Nat.le_ceil A₀
    push_cast
    linarith
  obtain ⟨D, hD, hraw⟩ := raw_prime_real_scale_natural_log_saving K R hR
  refine ⟨D, hD.le, ?_⟩
  filter_upwards [hraw, Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (1:ℝ)), eventually_ge_atTop (1:ℝ)]
    with y hy hlogy hy1
  intro f a b inst χ hprim hne hfC hay hab hby
  have hf2 : 2 ≤ f := by
    have hfpos : 0 < f := NeZero.pos f
    by_contra hh
    have hf1 : f = 1 := by omega
    subst f
    exact hne (Subsingleton.elim _ _)
  have hfR : (f:ℝ) ≤ Real.log y ^ R := by
    have hpow : Real.log y ^ C₀ ≤ Real.log y ^ R := by
      simpa only [Real.rpow_natCast] using
        (Real.rpow_le_rpow_of_exponent_le hlogy hCR)
    exact hfC.trans hpow
  have hb := hy f a b χ hprim hf2 hfR hay hab hby
  have hlognonneg : 0 ≤ Real.log y := by linarith
  have hpow : Real.log y ^ (-(K+1:ℝ)) ≤ Real.log y ^ (-A₀) :=
    Real.rpow_le_rpow_of_exponent_le hlogy (by linarith)
  have hdeneq : Real.log y ^ (-(K+1:ℝ)) =
      (Real.log y ^ (K+1))⁻¹ := by
    rw [Real.rpow_neg hlognonneg]
    congr 1
    calc
      Real.log y ^ ((K:ℝ)+1) =
          Real.log y ^ ((K+1:ℕ):ℝ) := by
        congr 1
        push_cast
        ring
      _ = Real.log y ^ (K+1) := Real.rpow_natCast _ _
  calc
    ‖∑ p ∈ Finset.Ioc a b, if p.Prime then χ p else 0‖ ≤
      D*y / Real.log y ^ (K+1) := hb
    _ = D*y * Real.log y ^ (-(K+1:ℝ)) := by
      rw [hdeneq, div_eq_mul_inv]
    _ ≤ D*y * Real.log y ^ (-A₀) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hD.le (by linarith))
end Green64Analytic.SourceSW

end

/-! ## ExactPrimeUtility -/

section

open Filter Topology Real
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 8000000

def SourcePrimeSiegelWalfisz : Prop :=
  ∀ C A : ℝ, 0 < C → 0 < A →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ y : ℝ in atTop,
      ∀ (f a b : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f),
        χ.IsPrimitive → χ ≠ 1 → (f:ℝ) ≤ (Real.log y)^C →
        y ≤ (a:ℝ)+1 → a ≤ b → (b:ℝ) ≤ 2*y →
        ‖∑ p ∈ Finset.Ioc a b, if p.Prime then χ p else 0‖ ≤
          K*y*(Real.log y)^(-A)

theorem sourcePrimeSiegelWalfisz_unconditional : SourcePrimeSiegelWalfisz := by
  exact Green64Analytic.SourceSW.sourcePrimeSiegelWalfisz_exact_body

theorem source_abel_norm_bound (f g : ℕ → ℂ) (N : ℕ) (H : ℝ)
    (hH : 0 ≤ H) (hg : ∀ k, k ≤ N → ‖∑ i ∈ Finset.range k, g i‖ ≤ H) :
    ‖∑ i ∈ Finset.range N, f i * g i‖ ≤
      H * (‖f (N-1)‖ + ∑ i ∈ Finset.range (N-1), ‖f (i+1)-f i‖) := by
  have _ := hH
  have hab := Finset.sum_range_by_parts f g N
  simp only [smul_eq_mul] at hab
  rw [hab]
  calc
    _ ≤ ‖f (N-1) * (∑ i ∈ Finset.range N, g i)‖ +
        ‖∑ i ∈ Finset.range (N-1),
          (f (i+1)-f i) * (∑ j ∈ Finset.range (i+1), g j)‖ := norm_sub_le _ _
    _ ≤ ‖f (N-1)‖ * H +
        ∑ i ∈ Finset.range (N-1), ‖f (i+1)-f i‖ * H := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hg N (le_refl _)) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact hg (i+1) (by have := Finset.mem_range.mp hi; omega)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem source_prime_first_factor_iff_rough_cofactor
    (p m : ℕ) (hp : p.Prime) (hm : 2 ≤ m) :
    (p*m).minFac = p ↔ p ≤ m.minFac := by
  have hpm4 : 4 ≤ p*m := by
    calc
      4 = 2*2 := by norm_num
      _ ≤ p*m := Nat.mul_le_mul hp.two_le hm
  have hpm : p*m ≠ 1 := by omega
  have hqprime : (p*m).minFac.Prime := Nat.minFac_prime hpm
  constructor
  · intro heq
    have hmminprime : m.minFac.Prime :=
      Nat.minFac_prime (by omega : m ≠ 1)
    have hd : m.minFac ∣ p*m := (Nat.minFac_dvd m).trans (dvd_mul_left m p)
    have hle := Nat.minFac_le_of_dvd hmminprime.two_le hd
    rwa [heq] at hle
  · intro hrough
    apply Nat.le_antisymm
    · exact Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p m)
    · have hdiv : (p*m).minFac ∣ p*m := Nat.minFac_dvd _
      rcases (hqprime.dvd_mul).mp hdiv with hd | hd
      · have heq : (p*m).minFac = p :=
          (Nat.prime_dvd_prime_iff_eq hqprime hp).mp hd
        exact heq.ge
      · have hle : m.minFac ≤ (p*m).minFac :=
          Nat.minFac_le_of_dvd hqprime.two_le hd
        exact hrough.trans hle

noncomputable def sourcePresieveReal (x : ℝ) : ℝ :=
  Real.exp (Real.sqrt (Real.log x))

theorem source_presieve_real_le_power
    (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ x : ℝ in atTop, sourcePresieveReal x ≤ x^θ := by
  let c : ℝ := (θ⁻¹)^2
  have hθ2 : θ^2 * c = 1 := by
    dsimp [c]
    field_simp
  have hLarge := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 c))
  filter_upwards [hLarge, eventually_gt_atTop (1:ℝ)] with x hL hx
  have hxpos : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := (Real.log_pos hx).le
  have h1 : 1 ≤ Real.log x := (le_max_left 1 c).trans hL
  have hc : c ≤ Real.log x := (le_max_right 1 c).trans hL
  have hthetaL : 1 ≤ θ^2 * Real.log x := by
    calc
      1 = θ^2*c := hθ2.symm
      _ ≤ θ^2*Real.log x :=
        mul_le_mul_of_nonneg_left hc (sq_nonneg θ)
  have hsq : Real.log x ≤ (θ*Real.log x)^2 := by
    have hmul := mul_le_mul_of_nonneg_right hthetaL hlog
    nlinarith
  have hsqrt : Real.sqrt (Real.log x) ≤ θ*Real.log x := by
    have hr : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
    have ht : 0 ≤ θ*Real.log x := mul_nonneg hθ.le hlog
    nlinarith [Real.sq_sqrt hlog]
  change Real.exp (Real.sqrt (Real.log x)) ≤ x^θ
  rw [Real.rpow_def_of_pos hxpos]
  exact Real.exp_le_exp.mpr (by nlinarith [hsqrt])
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD20MellinVariation -/

section

open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
noncomputable def sourceD20Mellin (t x : ℝ) : ℂ :=
  (x:ℂ)^((-1:ℂ)+Complex.I*(t:ℂ))
lemma sourceD20_mellin_norm (t x : ℝ) (hx : 0<x) :
    ‖sourceD20Mellin t x‖=x⁻¹ := by
  unfold sourceD20Mellin
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Real.rpow_neg_one]
lemma sourceD20_mellin_derivative (t x : ℝ) (hx : 0<x) :
    HasDerivAt (sourceD20Mellin t)
      (((-1:ℂ)+Complex.I*(t:ℂ))*(x:ℂ)^((-1:ℂ)+Complex.I*(t:ℂ)-1)) x := by
  apply hasDerivAt_ofReal_cpow_const hx.ne'
  intro he
  have hre := congrArg Complex.re he
  simp at hre
lemma sourceD20_mellin_derivative_bound (t a x : ℝ) (ha : 0<a) (hax : a≤x) :
    ‖((-1:ℂ)+Complex.I*(t:ℂ))*(x:ℂ)^((-1:ℂ)+Complex.I*(t:ℂ)-1)‖ ≤
      (1+|t|)/a^2 := by
  have hx := ha.trans_le hax
  have hc : ‖(-1:ℂ)+Complex.I*(t:ℂ)‖ ≤ 1+|t| := by
    simpa using (norm_add_le (-1:ℂ) (Complex.I*(t:ℂ)))
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have he : (((-1:ℂ)+Complex.I*(t:ℂ)-1).re)=(-2:ℝ) := by norm_num
  rw [he]
  have hr : x^(-2:ℝ)=(x^2)⁻¹ := by rw [Real.rpow_neg hx.le]; norm_num
  rw [hr]
  calc
    _ ≤ (1+|t|)*(x^2)⁻¹ := mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ (1+|t|)*(a^2)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (inv_le_inv₀ (sq_pos_of_pos hx) (sq_pos_of_pos ha)).mpr (by nlinarith)
    _ = _ := by ring
/-- Actual complex Mellin variation, not a free Lipschitz hypothesis. -/
theorem sourceD20_mellin_step (t a x : ℝ) (ha : 0<a) (hax : a≤x) :
    ‖sourceD20Mellin t (x+1)-sourceD20Mellin t x‖ ≤ (1+|t|)/a^2 := by
  have hder : ∀ y ∈ Set.Icc x (x+1),
      HasDerivWithinAt (sourceD20Mellin t)
        (((-1:ℂ)+Complex.I*(t:ℂ))*(y:ℂ)^((-1:ℂ)+Complex.I*(t:ℂ)-1)) (Set.Icc x (x+1)) y := by
    intro y hy
    exact (sourceD20_mellin_derivative t y (ha.trans_le (hax.trans hy.1))).hasDerivWithinAt
  have hb : ∀ y ∈ Set.Icc x (x+1),
      ‖((-1:ℂ)+Complex.I*(t:ℂ))*(y:ℂ)^((-1:ℂ)+Complex.I*(t:ℂ)-1)‖ ≤ (1+|t|)/a^2 :=
    fun y hy => sourceD20_mellin_derivative_bound t a y ha (hax.trans hy.1)
  have hh := (convex_Icc x (x+1)).norm_image_sub_le_of_norm_hasDerivWithin_le hder hb
    (show x ∈ Set.Icc x (x+1) by constructor <;> linarith)
    (show x+1 ∈ Set.Icc x (x+1) by constructor <;> linarith)
  simpa only [add_sub_cancel_left,norm_one,mul_one] using hh
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD20MellinAbel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
lemma sourceD20_sum_Icc_range (a N : ℕ) (f : ℕ → ℂ) (hN : 0 < N) :
    (∑ n ∈ Finset.Icc a (a+N-1),f n)=∑ i ∈ Finset.range N,f (a+i) := by
  symm
  apply Finset.sum_bij (fun i _ => a+i)
  · intro i hi; apply Finset.mem_Icc.mpr; have := Finset.mem_range.mp hi; omega
  · intro i hi j hj he; omega
  · intro n hn; refine ⟨n-a,Finset.mem_range.mpr ?_,?_⟩ <;> have := Finset.mem_Icc.mp hn <;> omega
  · intro i hi; rfl
/-- Abel transport on an actual positive dyad for the exact complex Mellin weight. -/
theorem sourceD20_mellin_abel (a N : ℕ) (ha : 2 ≤ a) (hN : 0<N) (hNa : N-1 ≤ a)
    (g : ℕ → ℂ) (t H : ℝ) (hH : 0≤H)
    (hpref : ∀ k, k≤N → ‖∑ i ∈ Finset.range k,g (a+i)‖≤H) :
    ‖∑ i ∈ Finset.range N,g (a+i)*sourceD20Mellin t (a+i)‖ ≤ H*(2+|t|)/(a:ℝ) := by
  have _ := hN
  let f := fun i : ℕ => sourceD20Mellin t (a+i)
  have haR : (0:ℝ)<a := by exact_mod_cast (show 0<a by omega)
  have hf : ‖f (N-1)‖ ≤ (a:ℝ)⁻¹ := by
    rw [sourceD20_mellin_norm t _ (by positivity)]
    exact (inv_le_inv₀ (by positivity) haR).mpr (by linarith [Nat.cast_nonneg (α := ℝ) (N-1)])
  have hs : ∀ i ∈ Finset.range (N-1),‖f (i+1)-f i‖ ≤ (1+|t|)/(a:ℝ)^2 := by
    intro i hi
    simpa only [f,Nat.cast_add,Nat.cast_one,add_assoc] using
      sourceD20_mellin_step t a (a+i) haR (by linarith [Nat.cast_nonneg (α := ℝ) i])
  have hsum : (∑ i ∈ Finset.range (N-1),‖f (i+1)-f i‖) ≤
      (a:ℝ)*((1+|t|)/(a:ℝ)^2) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (N-1),(1+|t|)/(a:ℝ)^2 := Finset.sum_le_sum hs
      _ = ((N-1:ℕ):ℝ)*((1+|t|)/(a:ℝ)^2) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hNa) (by positivity)
  have hab := source_abel_norm_bound f (fun i => g (a+i)) N H hH hpref
  have he : (a:ℝ)⁻¹+(a:ℝ)*((1+|t|)/(a:ℝ)^2)=(2+|t|)/(a:ℝ) := by
    field_simp; ring
  have hh := hab.trans (mul_le_mul_of_nonneg_left (add_le_add hf hsum) hH)
  rw [he] at hh
  simpa only [f,mul_comm,mul_div_assoc] using hh
/-- Principal/unmodulated actual proxy discrepancy on every finite dyadic interval. -/
theorem sourceD20_mellin_delta_interval {Δ W y : ℝ} (hΔ : 0<Δ) (hWy : W≤y)
    (a b : ℕ) (ha : 2≤a) (hab : a≤b) (hba : b≤2*a) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc a b,(sourceD20FullDelta Δ W y n:ℂ)*sourceD20Mellin t n‖ ≤
      (8*(Real.exp Δ-1)+2/(a:ℝ))*(2+|t|) := by
  let N := b-a+1
  let H : ℝ := 2*((Real.exp Δ-1)*(b:ℝ)+1)
  have hcoef : 0≤Real.exp Δ-1 := sub_nonneg.mpr (Real.one_le_exp hΔ.le)
  have hH : 0≤H := by dsimp [H]; positivity
  have hN : 0<N := by dsimp [N]; omega
  have hNa : N-1≤a := by dsimp [N]; omega
  have hpref : ∀ k,k≤N → ‖∑ i ∈ Finset.range k,(sourceD20FullDelta Δ W y (a+i):ℂ)‖≤H := by
    intro k hk
    by_cases hk0 : k=0
    · subst k; simpa using hH
    · rw [←sourceD20_sum_Icc_range a k (fun n => (sourceD20FullDelta Δ W y n:ℂ)) (by omega),←Complex.ofReal_sum,
        Complex.norm_real,Real.norm_eq_abs]
      have hb' : a+k-1 ≤ b := by dsimp [N] at hk; omega
      exact (sourceD20_interval_raw_bound hΔ hWy a (a+k-1) ha).trans (by
        dsimp [H]; gcongr)
  have h := sourceD20_mellin_abel a N ha hN hNa
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) t H hH hpref
  have hend : a+N-1=b := by dsimp [N]; omega
  have hsumEq := sourceD20_sum_Icc_range a N
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)*sourceD20Mellin t n) hN
  simp only [hend,Nat.cast_add] at hsumEq
  rw [←hsumEq] at h
  have haR : (0:ℝ)<a := by exact_mod_cast (show 0<a by omega)
  have hbR : (b:ℝ)≤2*(a:ℝ) := by exact_mod_cast hba
  have hHup : H ≤ 8*(Real.exp Δ-1)*(a:ℝ)+2 := by
    have hmul := mul_le_mul_of_nonneg_left hbR hcoef
    have he : 0≤(Real.exp Δ-1)*(a:ℝ) := by positivity
    dsimp [H]; nlinarith
  have hdiv : H/(a:ℝ) ≤ 8*(Real.exp Δ-1)+2/(a:ℝ) := by
    calc
      _ ≤ (8*(Real.exp Δ-1)*(a:ℝ)+2)/(a:ℝ) := div_le_div_of_nonneg_right hHup haR.le
      _ = _ := by field_simp
  exact h.trans (by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hdiv (by positivity))
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD20PrimeMellinSW -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
/-- Unconditional primitive nonprincipal prime atom with the exact Mellin twist.
This does NOT yet sum the canonical rough-factor lists or the cell proxy. -/
theorem sourceD20_prime_mellin_SW (C D : ℝ) (hC : 0<C) (hD : 0<D) :
    ∃ K Y : ℝ,0≤K ∧ ∀ (a b q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      Y≤(a:ℝ) → 2≤a → a≤b → b≤2*a → χ.IsPrimitive → χ≠1 →
      (q:ℝ)≤(Real.log (a:ℝ))^C → ∀ t : ℝ,
      ‖∑ n ∈ Finset.Icc a b,if n.Prime then χ n*sourceD20Mellin t n else 0‖ ≤
        K*(2+|t|)*(Real.log (a:ℝ))^(-D) := by
  obtain ⟨K,hK,hSW⟩ := sourcePrimeSiegelWalfisz_unconditional C D hC hD
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hSW
  refine ⟨K,Y,hK,?_⟩
  intro a b q inst χ hYa ha hab hba hprim hnon hq t
  let : NeZero q := inst
  let N := b-a+1
  let H := K*(a:ℝ)*(Real.log (a:ℝ))^(-D)
  let g := fun n : ℕ => if n.Prime then χ n else 0
  have hH : 0≤H := by dsimp [H]; positivity
  have hN : 0<N := by dsimp [N]; omega
  have hpref : ∀ k,k≤N → ‖∑ i ∈ Finset.range k,g (a+i)‖≤H := by
    intro k hk
    by_cases h0 : k=0
    · subst k; simpa using hH
    · have hbk : a+k-1 ≤ b := by dsimp [N] at hk; omega
      have hbound := hY (a:ℝ) hYa q (a-1) (a+k-1) χ hprim hnon hq
        (by exact_mod_cast (show a ≤ (a-1)+1 by omega))
        (by omega) ((Nat.cast_le.mpr hbk).trans (by exact_mod_cast hba))
      have hset : Finset.Ioc (a-1) (a+k-1)=Finset.Icc a (a+k-1) := by
        ext n; simp only [Finset.mem_Ioc,Finset.mem_Icc]; omega
      rw [hset,sourceD20_sum_Icc_range a k _ (by omega)] at hbound
      exact hbound
  have h := sourceD20_mellin_abel a N ha hN (by dsimp [N];omega) g t H hH hpref
  have hsum := sourceD20_sum_Icc_range a N (fun n => g n*sourceD20Mellin t n) hN
  have hend : a+N-1=b := by dsimp [N];omega
  simp only [hend,Nat.cast_add] at hsum
  rw [←hsum] at h
  have haR : (0:ℝ)<a := by exact_mod_cast (show 0<a by omega)
  have he : H*(2+|t|)/(a:ℝ)=K*(2+|t|)*(Real.log (a:ℝ))^(-D) := by
    dsimp [H]
    field_simp
  rw [he] at h
  simpa only [g,ite_mul,zero_mul] using h
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD20AllPrimeCharacters -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
/-- Imprimitive nonprincipal characters reduce exactly, because q<a excludes nonunits. -/
theorem sourceD20_all_prime_mellin_SW (C D : ℝ) (hC : 0<C) (hD : 0<D) :
    ∃ K Y : ℝ,0≤K ∧ ∀ (a b q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      Y≤(a:ℝ) → 2≤a → a≤b → b≤2*a → q<a → χ≠1 →
      (q:ℝ)≤(Real.log (a:ℝ))^C → ∀ t : ℝ,
      ‖∑ n ∈ Finset.Icc a b,if n.Prime then χ n*sourceD20Mellin t n else 0‖ ≤
        K*(2+|t|)*(Real.log (a:ℝ))^(-D) := by
  obtain ⟨K,Y,hK,hbase⟩ := sourceD20_prime_mellin_SW C D hC hD
  refine ⟨K,Y,hK,?_⟩
  intro a b q inst χ hYa ha hab hba hqa hnon hq t
  let : NeZero q := inst
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim : χ.primitiveCharacter ≠ 1 := by
    intro hh
    have he := χ.changeLevel_primitiveCharacter
    rw [hh,DirichletCharacter.changeLevel_one] at he
    exact hnon he.symm
  have hcq : (χ.conductor:ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hbound := hbase a b χ.conductor χ.primitiveCharacter hYa ha hab hba
    χ.primitiveCharacter_isPrimitive hprim (hcq.trans hq) t
  have heq : (∑ n ∈ Finset.Icc a b,if n.Prime then χ n*sourceD20Mellin t n else 0) =
      ∑ n ∈ Finset.Icc a b,if n.Prime then χ.primitiveCharacter n*sourceD20Mellin t n else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · rw [ite_eq_left hp,ite_eq_left hp]
      have hnq : q<n := hqa.trans_le (Finset.mem_Icc.mp hn).1
      have hcop : n.Coprime q := hp.coprime_iff_not_dvd.mpr (by
        intro hd
        have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hd
        omega)
      have hZ : IsCoprime (n:ℤ) (q:ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
      have hv := χ.primitiveCharacter_apply_of_isCoprime hZ
      have he : χ n=χ.primitiveCharacter n := by simpa only [Int.cast_natCast] using hv.symm
      rw [he]
    · rw [ite_eq_right hp,ite_eq_right hp]
  rw [heq]
  exact hbound
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD20PrincipalCharacter -/

section

open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
lemma sourceD20_rough_coprime {W : ℝ} {n q : ℕ}
    (hn : sourceD20Rough W n) (hq : 0<q) (hqw : (q:ℝ)≤W) : n.Coprime q := by
  by_contra hh
  obtain ⟨p,hp,hpn,hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hh
  have h1 : (n.minFac:ℝ) ≤ p := by exact_mod_cast Nat.minFac_le_of_dvd hp.two_le hpn
  have h2 : (p:ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd hq hpq
  linarith [hn.2]
/-- The actual principal character equals one on the complete proxy-difference support. -/
theorem sourceD20_principal_term (Δ W y : ℝ) (hWy : W≤y)
    (q n : ℕ) (hq : 0<q) (hqw : (q:ℝ)≤W) :
    (sourceD20FullDelta Δ W y n:ℂ)*(1:DirichletCharacter ℂ q) n =
      (sourceD20FullDelta Δ W y n:ℂ) := by
  by_cases hz : sourceD20FullDelta Δ W y n=0
  · simp [hz]
  · have hr : sourceD20Rough W n := by
      by_contra hn
      exact hz (sourceD20_delta_support _ hWy n hn)
    have hu : IsUnit (n:ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr (sourceD20_rough_coprime hr hq hqw)
    rw [MulChar.one_apply hu,mul_one]
theorem sourceD20_principal_interval_bound {Δ W y : ℝ} (hΔ : 0<Δ) (hWy : W≤y)
    (a b q : ℕ) (ha : 2≤a) (hab : a≤b) (hba : b≤2*a)
    (hq : 0<q) (hqw : (q:ℝ)≤W) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc a b,(sourceD20FullDelta Δ W y n:ℂ)*
      (1:DirichletCharacter ℂ q) n*sourceD20Mellin t n‖ ≤
      (8*(Real.exp Δ-1)+2/(a:ℝ))*(2+|t|) := by
  simp_rw [sourceD20_principal_term Δ W y hWy q _ hq hqw]
  exact sourceD20_mellin_delta_interval hΔ hWy a b ha hab hba t
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD21FirstPrimeFibre -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- Exact smallest-prime decomposition, including a prime (cofactor one). -/
lemma sourceD21_minFac_mul (p d : ℕ) (hp : p.Prime) (hd : 1 ≤ d) :
    (d*p).minFac=p ↔ d=1 ∨ p≤d.minFac := by
  by_cases h : d=1
  · simp [h,hp.minFac_eq]
  · have hd2 : 2≤d := by omega
    simpa only [mul_comm d p,h,false_or] using
      source_prime_first_factor_iff_rough_cofactor p d hp hd2

noncomputable def sourceD21PrimePairs (a b : ℕ) (y : ℝ) : Finset (ℕ×ℕ) :=
  (Finset.Icc 1 b ×ˢ Finset.Icc 2 b).filter (fun dp =>
    a≤dp.1*dp.2 ∧ dp.1*dp.2≤b ∧ dp.2.Prime ∧ y<(dp.2:ℝ) ∧
    (dp.1=1 ∨ dp.2≤dp.1.minFac))

/-- No list-length or factorial surrogate: every rough integer occurs once. -/
theorem sourceD21_rough_first_prime_sum (a b : ℕ) (ha : 2≤a)
    (y : ℝ) (F : ℕ→ℂ) :
    (∑ n ∈ (Finset.Icc a b).filter (sourceD20Rough y),F n)=
      ∑ dp ∈ sourceD21PrimePairs a b y,F (dp.1*dp.2) := by
  symm
  apply Finset.sum_bij (fun dp _ => dp.1*dp.2)
  · intro dp hdp
    obtain ⟨hbox,hab,hbb,hp,hy,hmin⟩ := Finset.mem_filter.mp hdp
    have hd := (Finset.mem_Icc.mp (Finset.mem_product.mp hbox).1).1
    have he := (sourceD21_minFac_mul dp.2 dp.1 hp hd).mpr hmin
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hab,hbb⟩,
      (ha.trans hab),by simpa only [he] using hy⟩
  · intro dp hdp eq heq he
    obtain ⟨hdpbox,_,_,hp,_,hmin⟩ := Finset.mem_filter.mp hdp
    obtain ⟨heqbox,_,_,hq,_,hmineq⟩ := Finset.mem_filter.mp heq
    have hd := (Finset.mem_Icc.mp (Finset.mem_product.mp hdpbox).1).1
    have hd' := (Finset.mem_Icc.mp (Finset.mem_product.mp heqbox).1).1
    have hep := (sourceD21_minFac_mul dp.2 dp.1 hp hd).mpr hmin
    have heq' := (sourceD21_minFac_mul eq.2 eq.1 hq hd').mpr hmineq
    have hpeq : dp.2=eq.2 := hep.symm.trans ((congrArg Nat.minFac he).trans heq')
    apply Prod.ext
    · rw [←hpeq] at he
      exact Nat.eq_of_mul_eq_mul_right hp.pos he
    · exact hpeq
  · intro n hn
    obtain ⟨hnI,hnR⟩ := Finset.mem_filter.mp hn
    have hn2 := hnR.1
    have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hpn : n.minFac≤n := Nat.minFac_le (by omega)
    have hd : 1≤n/n.minFac := Nat.le_div_iff_mul_le hp.pos |>.mpr (by simpa using hpn)
    have he : (n/n.minFac)*n.minFac=n := Nat.div_mul_cancel (Nat.minFac_dvd n)
    have hmin := (sourceD21_minFac_mul n.minFac (n/n.minFac) hp hd).mp
      (by rw [he])
    refine ⟨(n/n.minFac,n.minFac),?_,he⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hd,?_⟩,
      Finset.mem_Icc.mpr ⟨hp.two_le,hpn.trans (Finset.mem_Icc.mp hnI).2⟩⟩,?_,?_,hp,hnR.2,hmin⟩
    · exact (Nat.div_le_self _ _).trans (Finset.mem_Icc.mp hnI).2
    · simpa only [he] using (Finset.mem_Icc.mp hnI).1
    · simpa only [he] using (Finset.mem_Icc.mp hnI).2
  · intro dp hdp; rfl

/-- Exact uncurried cofactor sum retains p^k with no coprimality condition. -/
theorem sourceD21_rough_first_prime_double_sum (a b : ℕ) (ha : 2≤a)
    (y : ℝ) (F : ℕ→ℂ) :
    (∑ n ∈ Finset.Icc a b,if sourceD20Rough y n then F n else 0)=
      ∑ d ∈ Finset.Icc 1 b, ∑ p ∈ Finset.Icc 2 b,
        if a≤d*p ∧ d*p≤b ∧ p.Prime ∧ y<(p:ℝ) ∧ (d=1 ∨ p≤d.minFac)
        then F (d*p) else 0 := by
  rw [←Finset.sum_filter,sourceD21_rough_first_prime_sum a b ha]
  simp only [sourceD21PrimePairs,Finset.sum_filter,Finset.sum_product]
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD21PrimeInterval -/

section

open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- The exact remaining prime interval for a fixed positive cofactor. -/
noncomputable def sourceD21PrimeInterval (a b d : ℕ) (y : ℝ) : Finset ℕ :=
  (Finset.Icc 2 b).filter (fun p => a≤d*p ∧ d*p≤b ∧ y<(p:ℝ) ∧
    (d=1 ∨ p≤d.minFac))

lemma sourceD21_prime_interval_between (a b d : ℕ) (y : ℝ)
    {l u p : ℕ} (hl : l∈sourceD21PrimeInterval a b d y)
    (hu : u∈sourceD21PrimeInterval a b d y) (hlp : l≤p) (hpu : p≤u) :
    p∈sourceD21PrimeInterval a b d y := by
  obtain ⟨hlI,hal,hbl,hyl,hml⟩ := Finset.mem_filter.mp hl
  obtain ⟨huI,hau,hbu,hyu,hmu⟩ := Finset.mem_filter.mp hu
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hlI).1.trans hlp,hpu.trans (Finset.mem_Icc.mp huI).2⟩,
    hal.trans (Nat.mul_le_mul_left d hlp),(Nat.mul_le_mul_left d hpu).trans hbu,
    hyl.trans_le (Nat.cast_le.mpr hlp),?_⟩
  exact hmu.imp_right (fun h => hpu.trans h)

/-- Nonempty fibres are genuine intervals in one dyad, including repeated primes. -/
theorem sourceD21_prime_interval_endpoints (a b d : ℕ) (y : ℝ)
    (hd : 1≤d) (hba : b≤2*a) (hne : (sourceD21PrimeInterval a b d y).Nonempty) :
    ∃ l u : ℕ, 2≤l ∧ l≤u ∧ u≤2*l ∧ y<(l:ℝ) ∧
      sourceD21PrimeInterval a b d y=Finset.Icc l u := by
  let I := sourceD21PrimeInterval a b d y
  let l := I.min' hne
  let u := I.max' hne
  have hl : l∈I := Finset.min'_mem I hne
  have hu : u∈I := Finset.max'_mem I hne
  have hlu : l≤u := Finset.le_max' I l hl
  obtain ⟨hlI,hal,hbl,hyl,hml⟩ := Finset.mem_filter.mp hl
  obtain ⟨huI,hau,hbu,hyu,hmu⟩ := Finset.mem_filter.mp hu
  refine ⟨l,u,(Finset.mem_Icc.mp hlI).1,hlu,?_,hyl,?_⟩
  · have hdpos : 0<d := by omega
    have hm : d*u≤d*(2*l) := calc
      d*u ≤ b := hbu
      _ ≤ 2*a := hba
      _ ≤ 2*(d*l) := Nat.mul_le_mul_left 2 hal
      _ = d*(2*l) := by ring
    exact Nat.le_of_mul_le_mul_left hm hdpos
  · apply Finset.Subset.antisymm
    · intro p hp
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le I p hp,Finset.le_max' I p hp⟩
    · intro p hp
      exact sourceD21_prime_interval_between a b d y hl hu
        (Finset.mem_Icc.mp hp).1 (Finset.mem_Icc.mp hp).2
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD21PrimeFibreSW -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- Uniform SW on the exact cofactor prime fibre. No extra prime enumeration. -/
theorem sourceD21_prime_fibre_SW (C D : ℝ) (hC : 0<C) (hD : 0<D) :
    ∃ K Y : ℝ, 0≤K ∧ ∀ (a b d q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (y : ℝ), Y≤y → 2≤y → 1≤d → b≤2*a → (q:ℝ)≤y → χ≠1 →
      (q:ℝ)≤(Real.log y)^C → ∀ t : ℝ,
      ‖∑ p ∈ sourceD21PrimeInterval a b d y,
        if p.Prime then χ p*sourceD20Mellin t p else 0‖ ≤
      K*(2+|t|)*(Real.log y)^(-D) := by
  obtain ⟨K,Y,hK,hSW⟩ := sourceD20_all_prime_mellin_SW C D hC hD
  refine ⟨K,Y,hK,?_⟩
  intro a b d q inst χ y hY hy hd hba hqy hχ hq t
  by_cases hne : (sourceD21PrimeInterval a b d y).Nonempty
  · obtain ⟨l,u,hl,hlu,hul,hyl,he⟩ := sourceD21_prime_interval_endpoints a b d y hd hba hne
    have hlog : Real.log y≤Real.log (l:ℝ) := Real.log_le_log (by linarith) hyl.le
    have hlogpos : 0<Real.log y := Real.log_pos (by linarith)
    have hqlog : (q:ℝ)≤(Real.log (l:ℝ))^C :=
      hq.trans (Real.rpow_le_rpow hlogpos.le hlog hC.le)
    have hql : q<l := by exact_mod_cast hqy.trans_lt hyl
    have hbound := hSW l u q χ (hY.trans hyl.le) hl hlu hul hql hχ hqlog t
    rw [he]
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hlogpos hlog (by linarith)) (by positivity))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty,norm_zero]
    have hlog : 0≤Real.log y := Real.log_nonneg (by linarith)
    exact mul_nonneg (mul_nonneg hK (by positivity)) (Real.rpow_nonneg hlog _)

lemma sourceD21_twisted_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (d p : ℕ) :
    χ (d*p)*sourceD20Mellin t (d*p)=
      (χ d*sourceD20Mellin t d)*(χ p*sourceD20Mellin t p) := by
  simp only [map_mul,sourceD20Mellin,Complex.ofReal_mul,Complex.ofReal_natCast]
  rw [Complex.natCast_mul_natCast_cpow]
  ring

/-- Exact multiplicative Mellin factorization of the genuine rough test. -/
theorem sourceD21_rough_mellin_reindex (a b : ℕ) (ha : 2≤a) (y t : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.Icc a b,if sourceD20Rough y n then χ n*sourceD20Mellin t n else 0)=
      ∑ d ∈ Finset.Icc 1 b,(χ d*sourceD20Mellin t d)*
        (∑ p ∈ sourceD21PrimeInterval a b d y,if p.Prime then χ p*sourceD20Mellin t p else 0) := by
  rw [sourceD21_rough_first_prime_double_sum a b ha]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [sourceD21PrimeInterval,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hg : a≤d*p ∧ d*p≤b ∧ y<(p:ℝ) ∧ (d=1 ∨ p≤d.minFac)
  · by_cases hpr : p.Prime
    · have hg' : a≤d*p ∧ d*p≤b ∧ p.Prime ∧ y<(p:ℝ) ∧ (d=1 ∨ p≤d.minFac) :=
        ⟨hg.1,hg.2.1,hpr,hg.2.2.1,hg.2.2.2⟩
      rw [ite_eq_left hg',ite_eq_left hg,ite_eq_left hpr]
      simpa only [Nat.cast_mul] using sourceD21_twisted_mul χ t d p
    · simp [hg,hpr]
  · have hnot : ¬(a≤d*p ∧ d*p≤b ∧ p.Prime ∧ y<(p:ℝ) ∧ (d=1 ∨ p≤d.minFac)) :=
      fun h => hg ⟨h.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩
    simp only [ite_eq_right hg,ite_eq_right hnot,mul_zero]
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD21RoughCharacterSW -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- Genuine nonprincipal rough-number cancellation. Only ONE harmonic cofactor
sum is paid; prime multiplicities require neither enumeration nor a new hypothesis. -/
theorem sourceD21_rough_character_SW (C D : ℝ) (hC : 0<C) (hD : 0<D) :
    ∃ K Y : ℝ, 0≤K ∧ ∀ (a b q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (y : ℝ), Y≤y → 2≤y → 2≤a → a≤b → b≤2*a → (q:ℝ)≤y → χ≠1 →
      (q:ℝ)≤(Real.log y)^C → ∀ t : ℝ,
      ‖∑ n ∈ Finset.Icc a b,if sourceD20Rough y n then χ n*sourceD20Mellin t n else 0‖ ≤
      K*(2+|t|)*(Real.log y)^(-D)*(1+Real.log (b:ℝ)) := by
  obtain ⟨K,Y,hK,hSW⟩ := sourceD21_prime_fibre_SW C D hC hD
  refine ⟨K,Y,hK,?_⟩
  intro a b q inst χ y hY hy ha hab hba hqy hχ hq t
  let H := K*(2+|t|)*(Real.log y)^(-D)
  have hH : 0≤H := by
    have hlog : 0≤Real.log y := Real.log_nonneg (by linarith)
    exact mul_nonneg (mul_nonneg hK (by positivity)) (Real.rpow_nonneg hlog _)
  rw [sourceD21_rough_mellin_reindex a b ha]
  have hterm : ∀ d∈Finset.Icc 1 b,
      ‖(χ d*sourceD20Mellin t d)*
        (∑ p ∈ sourceD21PrimeInterval a b d y,if p.Prime then χ p*sourceD20Mellin t p else 0)‖ ≤
      (d:ℝ)⁻¹*H := by
    intro d hd
    have hdpos : (0:ℝ)<d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hc := χ.norm_le_one (d:ZMod q)
    have hf : ‖χ d*sourceD20Mellin t d‖≤(d:ℝ)⁻¹ := by
      rw [norm_mul,sourceD20_mellin_norm t d hdpos]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr hdpos.le)
    rw [norm_mul]
    exact mul_le_mul hf
      (hSW a b d q χ y hY hy (Finset.mem_Icc.mp hd).1 hba hqy hχ hq t)
      (norm_nonneg _) (inv_nonneg.mpr hdpos.le)
  have hsum : (∑ d ∈ Finset.Icc 1 b,(d:ℝ)⁻¹)≤1+Real.log (b:ℝ) := by
    have he : (∑ d ∈ Finset.Icc 1 b,(d:ℝ)⁻¹)=(harmonic b:ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    rw [he]
    exact harmonic_le_one_add_log b
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 b,‖(χ d*sourceD20Mellin t d)*
        (∑ p ∈ sourceD21PrimeInterval a b d y,if p.Prime then χ p*sourceD20Mellin t p else 0)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 b,(d:ℝ)⁻¹*H := Finset.sum_le_sum hterm
    _ = (∑ d ∈ Finset.Icc 1 b,(d:ℝ)⁻¹)*H := by rw [Finset.sum_mul]
    _ ≤ (1+Real.log (b:ℝ))*H := mul_le_mul_of_nonneg_right hsum hH
    _ = _ := by dsimp [H]; ring
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD20MeshRate -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
/-- All powers and endpoints are uniform once B,S,beta are fixed. -/
theorem sourceD20_mesh_scalar (B S β : ℝ) (hB : 0<B) (hS : 2*B<S) (hβ : 0<β) :
    ∀ᶠ L : ℝ in atTop, ∀ A t : ℝ, Real.exp (β*L)≤A → |t|≤L^B →
      (8*(Real.exp (L^(-S))-1)+2/A)*(2+|t|) ≤ L^(-B) := by
  have hr : Tendsto (fun L : ℝ => L^(2*B-S)) atTop (𝓝 0) := by
    simpa only [neg_sub] using (tendsto_rpow_neg_atTop (sub_pos.mpr hS))
  have he := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2*B) β hβ
  have ht : Tendsto (fun L : ℝ => 48*L^(2*B-S)+6*(L^(2*B)*Real.exp (-β*L))) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using (hr.const_mul 48).add (he.const_mul 6)
  filter_upwards [ht.eventually_lt_const (by norm_num : (0:ℝ)<1),eventually_ge_atTop (1:ℝ)]
    with L hsmall hL
  intro A t hA htt
  have hLp : 0<L := by linarith
  have hAp : 0<A := (Real.exp_pos _).trans_le hA
  have hpow : 1≤L^B := Real.one_le_rpow hL hB.le
  have hmesh0 : 0≤L^(-S) := Real.rpow_nonneg hLp.le _
  have hmesh1 : L^(-S)≤1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL (show -S≤0 by linarith)
  have hexp : Real.exp (L^(-S))-1 ≤ 2*L^(-S) := by
    have hh := Real.abs_exp_sub_one_le (show |L^(-S)|≤1 by rwa [abs_of_nonneg hmesh0])
    exact (le_abs_self _).trans (by simpa only [abs_of_nonneg hmesh0] using hh)
  have hInv : 2/A ≤ 2*Real.exp (-β*L) := by
    have hh := (inv_le_inv₀ hAp (Real.exp_pos (β*L))).mpr hA
    have heq : (Real.exp (β*L))⁻¹=Real.exp (-β*L) := by rw [←Real.exp_neg]; congr 1; ring
    rw [heq] at hh
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤2)
  have hbt : 2+|t|≤3*L^B := by linarith
  have hraw : (8*(Real.exp (L^(-S))-1)+2/A)*(2+|t|) ≤
      (16*L^(-S)+2*Real.exp (-β*L))*(3*L^B) := by
    apply mul_le_mul (by linarith) hbt (by positivity) (by positivity)
  have hp1 : L^(-S)*L^B*L^B=L^(2*B-S) := by
    rw [←Real.rpow_add hLp,←Real.rpow_add hLp]
    congr 1; ring
  have hp2 : L^B*L^B=L^(2*B) := by rw [←Real.rpow_add hLp]; congr 1; ring
  have halg : (16*L^(-S)+2*Real.exp (-β*L))*(3*L^B)*L^B =
      48*L^(2*B-S)+6*(L^(2*B)*Real.exp (-β*L)) := by
    calc
      _ = 48*(L^(-S)*L^B*L^B)+6*((L^B*L^B)*Real.exp (-β*L)) := by ring
      _ = _ := by rw [hp1,hp2]
  have hnorm := mul_le_mul_of_nonneg_right hraw (Real.rpow_nonneg hLp.le B)
  rw [halg] at hnorm
  have hout : (8*(Real.exp (L^(-S))-1)+2/A)*(2+|t|) ≤ 1/L^B :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hLp B)).mpr (hnorm.trans hsmall.le)
  simpa only [one_div,Real.rpow_neg hLp.le] using hout
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD20PrincipalSaving -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
lemma sourceD20_log_moduli_below_W (B : ℝ) (hB : 0<B) :
    ∀ᶠ L : ℝ in atTop,L^B ≤ Real.exp (Real.sqrt L) := by
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).bound
    (show (0:ℝ)<1/B by positivity)
  filter_upwards [hsmall,eventually_gt_atTop (1:ℝ)] with L hs hL
  have hLp : 0<L := by linarith
  have hl : 0≤Real.log L := Real.log_nonneg hL.le
  have hp : 0≤L^(1/2:ℝ) := Real.rpow_nonneg hLp.le _
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hl,abs_of_nonneg hp] at hs
  have hm := mul_le_mul_of_nonneg_left hs hB.le
  have he : B*((1/B)*L^(1/2:ℝ))=Real.sqrt L := by
    rw [←mul_assoc,mul_one_div_cancel hB.ne',one_mul,Real.sqrt_eq_rpow]
  rw [he] at hm
  rw [Real.rpow_def_of_pos hLp]
  exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hm)
/-- Full-cell rough proxy: unconditional uniform principal-character Mellin saving.
No positivity assumption on any cell denominator is required. -/
theorem sourceD20_actual_principal_saving (B S β γ : ℝ)
    (hB : 0<B) (hS : 2*B<S) (hβ : 0<β) (hγ : 0<γ) :
    ∀ᶠ L : ℝ in atTop,∀ a b q : ℕ, 2≤a → a≤b → b≤2*a →
      Real.exp (β*L)≤(a:ℝ) → 0<q → (q:ℝ)≤L^B → ∀ t : ℝ,|t|≤L^B →
      ‖∑ n ∈ Finset.Icc a b,
        (sourceD20FullDelta (L^(-S)) (Real.exp (Real.sqrt L)) ((Real.exp L)^γ) n:ℂ)*
          (1:DirichletCharacter ℂ q) n*sourceD20Mellin t n‖ ≤ L^(-B) := by
  have hW := Real.tendsto_exp_atTop.eventually (source_presieve_real_le_power γ hγ)
  filter_upwards [sourceD20_mesh_scalar B S β hB hS hβ,sourceD20_log_moduli_below_W B hB,
    hW,eventually_gt_atTop (0:ℝ)] with L hscalar hmod hWy hL
  intro a b q ha hab hba hsize hq hqB t ht
  have hWy' : Real.exp (Real.sqrt L) ≤ (Real.exp L)^γ := by
    simpa only [sourcePresieveReal,Real.log_exp] using hWy
  have hraw := sourceD20_principal_interval_bound (Real.rpow_pos_of_pos hL (-S)) hWy'
    a b q ha hab hba hq (hqB.trans hmod) t
  exact hraw.trans (hscalar a t hsize ht)
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD20RestrictedPrincipal -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
/-- Restriction is imposed AFTER full-cell normalization. Any test interval is allowed. -/
theorem sourceD20_restricted_principal_saving (B S β γ : ℝ)
    (hB : 0<B) (hS : 2*B<S) (hβ : 0<β) (hγ : 0<γ) :
    ∀ᶠ L : ℝ in atTop,∀ l u a b q : ℕ, 2≤l → u≤2*l →
      Real.exp (β*L)≤(l:ℝ) → 0<q → (q:ℝ)≤L^B → ∀ t : ℝ,|t|≤L^B →
      ‖∑ n ∈ Finset.Icc a b,
        (if n ∈ Finset.Icc l u then
          (sourceD20FullDelta (L^(-S)) (Real.exp (Real.sqrt L)) ((Real.exp L)^γ) n:ℂ)
          else 0) * (1:DirichletCharacter ℂ q) n*sourceD20Mellin t n‖ ≤ L^(-B) := by
  filter_upwards [sourceD20_actual_principal_saving B S β γ hB hS hβ hγ,
    eventually_gt_atTop (0:ℝ)] with L hs hL
  intro l u a b q hl hu hsize hq hqB t ht
  let f := fun n => (sourceD20FullDelta (L^(-S)) (Real.exp (Real.sqrt L)) ((Real.exp L)^γ) n:ℂ)*
    (1:DirichletCharacter ℂ q) n*sourceD20Mellin t n
  have he : (∑ n ∈ Finset.Icc a b,
      (if n ∈ Finset.Icc l u then
        (sourceD20FullDelta (L^(-S)) (Real.exp (Real.sqrt L)) ((Real.exp L)^γ) n:ℂ) else 0)*
        (1:DirichletCharacter ℂ q) n*sourceD20Mellin t n) =
      ∑ n ∈ Finset.Icc (max l a) (min u b),f n := by
    simp only [ite_mul,zero_mul,←Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter,Finset.mem_Icc,max_le_iff,le_min_iff]
    tauto
  rw [he]
  by_cases hab : max l a ≤ min u b
  · exact hs (max l a) (min u b) q (hl.trans (le_max_left _ _)) hab
      (by omega) (hsize.trans (Nat.cast_le.mpr (le_max_left _ _))) hq hqB t ht
  · have hset : Finset.Icc (max l a) (min u b)=∅ := Finset.Icc_eq_empty_of_lt (lt_of_not_ge hab)
    rw [hset,Finset.sum_empty,norm_zero]
    exact Real.rpow_nonneg hL.le _
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD21RoughNonprincipal -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- Uniform saving for EVERY rough cutoff y >= exp(sqrt L), including the
proxy support itself. Constants do not depend on y, intervals, modulus or twist. -/
theorem sourceD21_rough_nonprincipal_saving (A B : ℝ) (hA : 0<A) (hB : 0<B) :
    ∀ᶠ L : ℝ in atTop, ∀ (a b q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (y t : ℝ), 2≤a → a≤b → b≤2*a → (b:ℝ)≤Real.exp (2*L) →
      Real.exp (Real.sqrt L)≤y → χ≠1 → (q:ℝ)≤L^B → |t|≤L^B →
      ‖∑ n ∈ Finset.Icc a b,if sourceD20Rough y n then χ n*sourceD20Mellin t n else 0‖ ≤ L^(-A) := by
  let D : ℝ := 2*(A+B+3)
  obtain ⟨K,Y,hK,hSW⟩ := sourceD21_rough_character_SW (2*B) D (by positivity) (by dsimp [D];positivity)
  have hYlarge := (Real.tendsto_exp_atTop.comp Real.tendsto_sqrt_atTop).eventually_ge_atTop (max Y 2)
  filter_upwards [hYlarge,sourceD20_log_moduli_below_W B hB,
    eventually_ge_atTop (max 1 (9*K+1))] with L hYL hmod hLarge
  intro a b q inst χ y t ha hab hba hb hWy hχ hq ht
  have hL : 1≤L := (le_max_left _ _).trans hLarge
  have hLp : 0<L := by linarith
  have hKL : 9*K+1≤L := (le_max_right _ _).trans hLarge
  have hy2 : 2≤y := ((le_max_right Y 2).trans hYL).trans hWy
  have hyY : Y≤y := ((le_max_left Y 2).trans hYL).trans hWy
  have hlog : Real.sqrt L≤Real.log y := by
    have hh := Real.log_le_log (Real.exp_pos _) hWy
    simpa only [Real.log_exp] using hh
  have hsqrt : 0<Real.sqrt L := Real.sqrt_pos.mpr hLp
  have hqlog : (q:ℝ)≤(Real.log y)^(2*B) := by
    have he : (Real.sqrt L)^(2*B)=L^B := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul hLp.le]
      congr 1; ring
    exact hq.trans (he.symm.le.trans (Real.rpow_le_rpow hsqrt.le hlog (by positivity)))
  have hraw := hSW a b q χ y hyY hy2 ha hab hba ((hq.trans hmod).trans hWy) hχ hqlog t
  have hpower : (Real.log y)^(-D)≤L^(-(A+B+3)) := by
    have hh := Real.rpow_le_rpow_of_nonpos hsqrt hlog (show -D≤0 by dsimp [D];linarith)
    have he : (Real.sqrt L)^(-D)=L^(-(A+B+3)) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul hLp.le]
      congr 1; dsimp [D]; ring
    exact hh.trans_eq he
  have hpow : 1≤L^B := Real.one_le_rpow hL hB.le
  have ht3 : 2+|t|≤3*L^B := by linarith
  have hlogb : Real.log (b:ℝ)≤2*L := by
    have hbp : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
    exact (Real.log_le_iff_le_exp hbp).mpr hb
  have hb3 : 1+Real.log (b:ℝ)≤3*L := by linarith
  have hlogb0 : 0≤1+Real.log (b:ℝ) := by
    have hh : 0≤Real.log (b:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤b by omega))
    linarith
  have hlogpow : 0≤(Real.log y)^(-D) := Real.rpow_nonneg (hsqrt.le.trans hlog) _
  have hbound : ‖∑ n ∈ Finset.Icc a b,if sourceD20Rough y n then χ n*sourceD20Mellin t n else 0‖ ≤
      (9*K)*L^B*L^(-(A+B+3))*L := by
    calc
      _ ≤ K*(2+|t|)*(Real.log y)^(-D)*(1+Real.log (b:ℝ)) := hraw
      _ ≤ K*(3*L^B)*L^(-(A+B+3))*(3*L) := by gcongr
      _ = _ := by ring
  have halg : L^B*L^(-(A+B+3))*L*L^A=L^(-2:ℝ) := by
    calc
      _ = L^B*L^(-(A+B+3))*L^(1:ℝ)*L^A := by rw [Real.rpow_one]
      _ = L^(B+(-(A+B+3))+1+A) := by rw [←Real.rpow_add hLp,←Real.rpow_add hLp,←Real.rpow_add hLp]
      _ = _ := by congr 1; ring
  have hnorm := mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hLp.le A)
  have hrw : ((9*K)*L^B*L^(-(A+B+3))*L)*L^A=(9*K)*L^(-2:ℝ) := by
    rw [mul_assoc (9*K),mul_assoc (9*K),mul_assoc (9*K),halg]
  rw [hrw] at hnorm
  have hsmall : (9*K)*L^(-2:ℝ)≤1 := by
    have hk2 : 9*K≤L^2 := by nlinarith
    have he : L^(-2:ℝ)=(L^2)⁻¹ := by rw [Real.rpow_neg hLp.le]; norm_num
    rw [he,←div_eq_mul_inv]
    exact (div_le_one (sq_pos_of_pos hLp)).mpr hk2
  have hout := (le_div_iff₀ (Real.rpow_pos_of_pos hLp A)).mpr (hnorm.trans hsmall)
  simpa only [one_div,Real.rpow_neg hLp.le] using hout
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD21ProxyCharacter -/

section

open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- Exact cellwise transport for the ACTUAL full-cell ratio, even at cut endpoints. -/
theorem sourceD21_proxy_character_bound (Δ W y t H : ℝ) (hΔ : 0<Δ) (hWy : W≤y)
    (a b : ℕ) (ha : 2≤a) (hab : a≤b) {q : ℕ} (χ : DirichletCharacter ℂ q) (hH : 0≤H)
    (hrough : ∀ l u : ℕ,a≤l → l≤u → u≤b →
      ‖∑ n ∈ Finset.Icc l u,if sourceD20Rough W n then χ n*sourceD20Mellin t n else 0‖≤H) :
    ‖∑ n ∈ Finset.Icc a b,(sourceD20FullProxy Δ W y n:ℂ)*χ n*sourceD20Mellin t n‖ ≤
      (((Finset.Icc a b).image (sourceD20CellIndex Δ)).card:ℝ)*H := by
  have _ := hab
  let I := Finset.Icc a b
  let J := I.image (sourceD20CellIndex Δ)
  let F := fun j => ∑ n ∈ I.filter (fun n => sourceD20CellIndex Δ n=j),
    (sourceD20FullProxy Δ W y n:ℂ)*χ n*sourceD20Mellin t n
  have hsum : (∑ j ∈ J,F j)=∑ n ∈ I,(sourceD20FullProxy Δ W y n:ℂ)*χ n*sourceD20Mellin t n :=
    Finset.sum_fiberwise_of_maps_to (fun n hn => Finset.mem_image_of_mem _ hn) _
  have hterm : ∀ j∈J,‖F j‖≤H := by
    intro j hj
    let C := sourceD20LogCell Δ j
    let c := sourceD20CellRatio C W y
    let T := I.filter (fun n => sourceD20CellIndex Δ n=j)
    have hcb := sourceD20_ratio_bounds C hWy
    have heq : F j=(c:ℂ)*(∑ n ∈ T,if sourceD20Rough W n then χ n*sourceD20Mellin t n else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hi := (Finset.mem_filter.mp hn).2
      simp only [sourceD20FullProxy,hi,sourceD20CellProxy]
      by_cases hr : sourceD20Rough W n
      · simp only [ite_eq_left hr]; exact mul_assoc _ _ _
      · simp only [ite_eq_right hr,Complex.ofReal_zero,zero_mul,mul_zero]
    have hc : ‖(c:ℂ)‖≤1 := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hcb.1]
      exact hcb.2
    have hTs : T=Finset.Icc (max a (⌊Real.exp ((j:ℝ)*Δ)⌋₊+1))
        (min b ⌊Real.exp (((j:ℝ)+1)*Δ)⌋₊) := sourceD21_cell_slice Δ hΔ a b j ha
    have hs : ‖∑ n ∈ T,if sourceD20Rough W n then χ n*sourceD20Mellin t n else 0‖≤H := by
      by_cases hn : T.Nonempty
      · rw [hTs] at hn ⊢
        exact hrough _ _ (le_max_left _ _) (Finset.nonempty_Icc.mp hn) (min_le_left _ _)
      · rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty,norm_zero]
        exact hH
    rw [heq,norm_mul]
    exact (mul_le_mul hc hs (norm_nonneg _) (by norm_num)).trans_eq (one_mul H)
  rw [←hsum]
  calc
    _ ≤ ∑ j∈J,‖F j‖ := norm_sum_le _ _
    _ ≤ ∑ _j∈J,H := Finset.sum_le_sum hterm
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; rfl
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD21FullNonprincipal -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

lemma sourceD21_delta_sum (Δ W y t : ℝ) (a b : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.Icc a b,(sourceD20FullDelta Δ W y n:ℂ)*χ n*sourceD20Mellin t n)=
      (∑ n ∈ Finset.Icc a b,if sourceD20Rough y n then χ n*sourceD20Mellin t n else 0)-
      ∑ n ∈ Finset.Icc a b,(sourceD20FullProxy Δ W y n:ℂ)*χ n*sourceD20Mellin t n := by
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn2 : 2 ≤ n <;>
    by_cases hy : y < (n.minFac : ℝ) <;>
    simp [sourceD20FullDelta, sourceD19RoughTest, sourceD20Rough,
      hn2, hy, Complex.ofReal_sub, sub_mul]

/-- Full nonprincipal discrepancy of the actual normalized cell proxy.
Both test and proxy are controlled, including all partial-cell intervals. -/
theorem sourceD21_full_nonprincipal_saving (B S : ℝ) (hB : 0<B) (hS : 0<S) :
    ∀ᶠ L : ℝ in atTop,∀ (a b q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (y t : ℝ),2≤a → a≤b → b≤2*a → (b:ℝ)≤Real.exp (2*L) →
      Real.exp (Real.sqrt L)≤y → χ≠1 → (q:ℝ)≤L^B → |t|≤L^B →
      ‖∑ n ∈ Finset.Icc a b,
        (sourceD20FullDelta (L^(-S)) (Real.exp (Real.sqrt L)) y n:ℂ)*χ n*sourceD20Mellin t n‖≤L^(-B) := by
  let A : ℝ := B+S+4
  filter_upwards [sourceD21_rough_nonprincipal_saving A B (by dsimp [A];positivity) hB,
    eventually_ge_atTop (2:ℝ)] with L hR hL
  intro a b q inst χ y t ha hab hba hb hWy hχ hq ht
  have hLp : 0<L := by linarith
  have hL1 : 1≤L := by linarith
  let Δ := L^(-S)
  let W := Real.exp (Real.sqrt L)
  let c := (((Finset.Icc a b).image (sourceD20CellIndex Δ)).card:ℝ)
  have hΔ : 0<Δ := Real.rpow_pos_of_pos hLp _
  have htest := hR a b q χ y t ha hab hba hb hWy hχ hq ht
  have hproxy := sourceD21_proxy_character_bound Δ W y t (L^(-A)) hΔ hWy a b ha hab χ
    (Real.rpow_nonneg hLp.le _) (by
      intro l u hal hlu hub
      exact hR l u q χ W t (ha.trans hal) hlu
        (hub.trans (hba.trans (Nat.mul_le_mul_left 2 hal)))
        ((Nat.cast_le.mpr hub).trans hb) le_rfl hχ hq ht)
  have hbound : ‖∑ n ∈ Finset.Icc a b,(sourceD20FullDelta Δ W y n:ℂ)*χ n*sourceD20Mellin t n‖≤
      (c+1)*L^(-A) := by
    rw [sourceD21_delta_sum]
    exact (norm_sub_le _ _).trans ((add_le_add htest hproxy).trans_eq (by dsimp [c];ring))
  have hlogb : Real.log (b:ℝ)≤2*L :=
    (Real.log_le_iff_le_exp (by exact_mod_cast (show 0<b by omega))).mpr hb
  have hcount := sourceD21_cell_count Δ hΔ a b ha hab
  have hex : L/Δ=L^(S+1) := by
    have hh := Real.rpow_add hLp S 1
    rw [Real.rpow_one] at hh
    dsimp [Δ]
    rw [Real.rpow_neg hLp.le,div_inv_eq_mul,hh,mul_comm]
  have hcount' : c≤2*L^(S+1)+2 := by
    have hh := div_le_div_of_nonneg_right hlogb hΔ.le
    rw [mul_div_assoc,hex] at hh
    linarith only [hcount,hh]
  have hp1 : 1≤L^(S+1) := Real.one_le_rpow hL1 (by linarith)
  have hc5 : c+1≤5*L^(S+1) := by linarith
  have hnorm := hbound.trans (mul_le_mul_of_nonneg_right hc5 (Real.rpow_nonneg hLp.le _))
  have hp : L^(S+1)*L^(-A)*L^B=L^(-3:ℝ) := by
    rw [←Real.rpow_add hLp,←Real.rpow_add hLp]
    congr 1; dsimp [A];ring
  have hscaled := mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg hLp.le B)
  have he : (5*L^(S+1)*L^(-A))*L^B=5*L^(-3:ℝ) := by
    calc
      _ = 5*(L^(S+1)*L^(-A)*L^B) := by ring
      _ = _ := by rw [hp]
  rw [he] at hscaled
  have hsmall : 5*L^(-3:ℝ)≤1 := by
    have hcube : 5≤L^3 := by nlinarith [sq_nonneg (L-2)]
    rw [Real.rpow_neg hLp.le]
    norm_num
    rw [←div_eq_mul_inv]
    exact (div_le_one (pow_pos hLp 3)).mpr hcube
  have hout := (le_div_iff₀ (Real.rpow_pos_of_pos hLp B)).mpr (hscaled.trans hsmall)
  simpa only [Δ,W,one_div,Real.rpow_neg hLp.le] using hout
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD21AllCharacterDiscrepancy -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- Principal and nonprincipal branches for the unchanged actual full-cell proxy. -/
theorem sourceD21_all_character_saving (B S β γ : ℝ)
    (hB : 0<B) (hS : 2*B<S) (hβ : 0<β) (hγ : 0<γ) :
    ∀ᶠ L : ℝ in atTop,∀ (a b q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2≤a → a≤b → b≤2*a → Real.exp (β*L)≤(a:ℝ) →
      (b:ℝ)≤Real.exp (2*L) → (q:ℝ)≤L^B → ∀ t : ℝ,|t|≤L^B →
      ‖∑ n ∈ Finset.Icc a b,
        (sourceD20FullDelta (L^(-S)) (Real.exp (Real.sqrt L)) ((Real.exp L)^γ) n:ℂ)*
          χ n*sourceD20Mellin t n‖≤L^(-B) := by
  have hW := Real.tendsto_exp_atTop.eventually (source_presieve_real_le_power γ hγ)
  filter_upwards [sourceD21_full_nonprincipal_saving B S hB (by linarith),
    sourceD20_actual_principal_saving B S β γ hB hS hβ hγ,hW] with L hnon hprin hWy
  intro a b q inst χ ha hab hba hsize hb hq t ht
  by_cases he : χ=1
  · subst χ
    exact hprin a b q ha hab hba hsize (Nat.pos_of_ne_zero (NeZero.ne q)) hq t ht
  · exact hnon a b q χ ((Real.exp L)^γ) t ha hab hba hb
      (by simpa only [sourcePresieveReal,Real.log_exp] using hWy) he hq ht

/-- Extra interval restrictions are imposed after FULL-cell normalization. -/
theorem sourceD21_restricted_all_character_saving (B S β γ : ℝ)
    (hB : 0<B) (hS : 2*B<S) (hβ : 0<β) (hγ : 0<γ) :
    ∀ᶠ L : ℝ in atTop,∀ (l u a b q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2≤l → u≤2*l → Real.exp (β*L)≤(l:ℝ) → (u:ℝ)≤Real.exp (2*L) →
      (q:ℝ)≤L^B → ∀ t : ℝ,|t|≤L^B →
      ‖∑ n ∈ Finset.Icc a b,
        (if n ∈ Finset.Icc l u then
          (sourceD20FullDelta (L^(-S)) (Real.exp (Real.sqrt L)) ((Real.exp L)^γ) n:ℂ)
          else 0)*χ n*sourceD20Mellin t n‖≤L^(-B) := by
  filter_upwards [sourceD21_all_character_saving B S β γ hB hS hβ hγ,
    eventually_gt_atTop (0:ℝ)] with L hsave hL
  intro l u a b q inst χ hl hu hsize hub hq t ht
  let f := fun n => (sourceD20FullDelta (L^(-S)) (Real.exp (Real.sqrt L)) ((Real.exp L)^γ) n:ℂ)*
    χ n*sourceD20Mellin t n
  have he : (∑ n ∈ Finset.Icc a b,
      (if n ∈ Finset.Icc l u then
        (sourceD20FullDelta (L^(-S)) (Real.exp (Real.sqrt L)) ((Real.exp L)^γ) n:ℂ) else 0)*
        χ n*sourceD20Mellin t n)=∑ n ∈ Finset.Icc (max l a) (min u b),f n := by
    simp only [ite_mul,zero_mul,←Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter,Finset.mem_Icc,max_le_iff,le_min_iff]
    tauto
  rw [he]
  by_cases hab : max l a ≤ min u b
  · exact hsave (max l a) (min u b) q χ (hl.trans (le_max_left _ _)) hab (by omega)
      (hsize.trans (Nat.cast_le.mpr (le_max_left _ _)))
      ((Nat.cast_le.mpr (min_le_left _ _)).trans hub) hq t ht
  · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hab),Finset.sum_empty,norm_zero]
    exact Real.rpow_nonneg hL.le _
end Green64Analytic.SourceBlockSieve

end

