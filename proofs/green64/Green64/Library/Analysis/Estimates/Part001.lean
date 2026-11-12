module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Tactic
public import Mathlib
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.MellinTransform
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.DiophantineApproximation.Basic

@[expose] public section

/-!
# Analysis / Estimates / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## Imports.PrimePowerProgressions -/

section

/- Adapted from lixiang90/chen_theorem@11dcca8fc3ab340358503278c46d72aef072a6e7,
formal/ChenTheorem/Lemma9/BombieriVinogradov/PrimeWeights.lean lines 9-57.
The definition of progressionPsi is adapted from Basic.lean; full source provenance
and Apache-2.0 attribution are in the task manifest. -/
open Filter Real
open scoped Classical
namespace Green64Imports
noncomputable def progressionPsi (x q a : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x,
    if n ≡ a [MOD q] then ArithmeticFunction.vonMangoldt n else 0

/-- The theta sum over primes in one arithmetic progression. -/
noncomputable def progressionTheta (x q a : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x,
    if n.Prime ∧ n ≡ a [MOD q] then Real.log n else 0

theorem progressionTheta_nonneg (x q a : ℕ) : 0 ≤ progressionTheta x q a := by
  apply Finset.sum_nonneg
  intro n hn
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.1.one_le)
  · exact le_rfl

theorem progressionTheta_le_psi (x q a : ℕ) :
    progressionTheta x q a ≤ progressionPsi x q a := by
  apply Finset.sum_le_sum
  intro n hn
  by_cases hp : n.Prime
  · simp only [hp, true_and, ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact le_rfl
  · simp only [hp, false_and, if_false]
    split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl

/-- The contribution of higher prime powers in a progression is bounded
by their contribution in the whole interval. -/
theorem progressionPsi_sub_theta_le (x q a : ℕ) :
    progressionPsi x q a - progressionTheta x q a ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hglobal : Chebyshev.psi x - Chebyshev.theta x =
      ∑ n ∈ Finset.Icc 1 x, if ¬n.Prime then ArithmeticFunction.vonMangoldt n else 0 := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
    congr 1
  rw [hglobal, progressionPsi, progressionTheta, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hp : n.Prime
  · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp only [hp, not_false_eq_true, if_true, false_and, if_false, sub_zero]
    split_ifs
    · exact le_rfl
    · exact ArithmeticFunction.vonMangoldt_nonneg

theorem abs_progressionTheta_sub_psi_le {x : ℕ} (hx : 1 ≤ x) (q a : ℕ) :
    |progressionTheta x q a - progressionPsi x q a| ≤
      2 * Real.sqrt x * Real.log x := by
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (progressionTheta_le_psi x q a))]
  exact (progressionPsi_sub_theta_le x q a).trans
    (Chebyshev.psi_sub_theta_le (by exact_mod_cast hx))
end Green64Imports

end

/-! ## HarmonicBudget -/

section

namespace Green64SourceC6

/-- Exact harmonic logarithm needed after counting rational phase bins.
No unproved asymptotic estimate or primitive-character hypothesis. -/
theorem source_harmonic_log_budget (q : ℕ) (hq : 1 ≤ q) :
    harmonic q ≤ 2 * Real.log (2 * (q : ℝ)) := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
  have hlogtwo : (1 : ℝ)/2 ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlog : Real.log (2 * (q : ℝ)) = Real.log 2 + Real.log (q : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hqpos)]
  have hH := harmonic_le_one_add_log q
  rw [hlog]
  linarith

end Green64SourceC6

end

/-! ## LastPrimePNT -/

section

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Green64Analytic.OrderedPrimeRough

/-- Literal natural-prime last-coordinate count with real cutoffs. -/
noncomputable def primeWindow (z y : ℝ) : Finset ℕ :=
  (Finset.Ioc (Nat.floor z) (Nat.floor y)).filter Nat.Prime

theorem primeWindow_card_pi_difference (z y : ℝ)
    (hz : 0 ≤ z) (hzy : z ≤ y) :
    ((primeWindow z y).card : ℝ) =
      (Nat.primeCounting (Nat.floor y) : ℝ) -
      (Nat.primeCounting (Nat.floor z) : ℝ) := by
  have _ := hz
  have hfloor : Nat.floor z ≤ Nat.floor y := Nat.floor_mono hzy
  have hsub : (Nat.floor z).primesLE ⊆ (Nat.floor y).primesLE :=
    Nat.primesLE_mono hfloor
  have heq : primeWindow z y =
      (Nat.floor y).primesLE \ (Nat.floor z).primesLE := by
    ext p
    simp only [primeWindow, Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hlo,hhi⟩,hpr⟩
      refine ⟨⟨hhi,hpr⟩,?_⟩
      intro hp
      omega
    · rintro ⟨⟨hhi,hpr⟩,hp⟩
      refine ⟨⟨?_,hhi⟩,hpr⟩
      by_contra hle
      exact hp ⟨by omega,hpr⟩
  have hsum : (primeWindow z y).card +
      (Nat.floor z).primeCounting = (Nat.floor y).primeCounting := by
    rw [← Nat.primesLE_card_eq_primeCounting (Nat.floor z),
      ← Nat.primesLE_card_eq_primeCounting (Nat.floor y), heq]
    exact Finset.card_sdiff_add_card_eq_card hsub
  have hsumReal : ((primeWindow z y).card : ℝ) +
      (Nat.primeCounting (Nat.floor z):ℝ) =
      (Nat.primeCounting (Nat.floor y):ℝ) := by
    exact_mod_cast hsum
  linarith


/-- Uniform elementary counting upper bound for π(z), including
noninteger and boundary real cutoffs. The +1 is harmless for
the last-prime PNT but retained exactly rather than silently dropped. -/
theorem primeCounting_floor_le_z_add_one (z : ℝ) (hz : 0 ≤ z) :
    (Nat.primeCounting (Nat.floor z) : ℝ) ≤ z + 1 := by
  have hsub : (Nat.floor z).primesLE ⊆
      Finset.range (Nat.floor z + 1) := by
    intro p hp
    have hle := (Nat.mem_primesLE.mp hp).1
    simp only [Finset.mem_range]
    omega
  have hcard := Finset.card_le_card hsub
  simp only [Finset.card_range, Nat.primesLE_card_eq_primeCounting] at hcard
  have hcast : (Nat.primeCounting (Nat.floor z):ℝ) ≤ (Nat.floor z:ℝ)+1 := by
    exact_mod_cast hcard
  linarith [Nat.floor_le hz]

/-- A quantitatively explicit last-prime PNT consequence, for any fixed
window z<=y, whose upper endpoint is beyond the classical PNT2 threshold.
The sole analytic premise is the standard uniform π(y) estimate. -/
theorem primeWindow_from_PNT2 (Y C z y : ℝ)
    (hz : 0 ≤ z) (hzy : z ≤ y) (hY : Y ≤ y)
    (hPNT2 : ∀ u : ℝ, Y ≤ u →
      |(Nat.primeCounting (Nat.floor u):ℝ) - u/Real.log u| ≤
        C*u/(Real.log u)^2) :
    y/Real.log y - C*y/(Real.log y)^2 - (z+1) ≤
      ((primeWindow z y).card : ℝ) := by
  have hp : -(C*y/(Real.log y)^2) ≤
      (Nat.primeCounting (Nat.floor y):ℝ) - y/Real.log y :=
    (abs_le.mp (hPNT2 y hY)).1
  have hq := primeCounting_floor_le_z_add_one z hz
  rw [primeWindow_card_pi_difference z y hz hzy]
  linarith


/-- Quantitative relative last-prime lower bound with explicit
two-part error budget: the PNT error and the excluded small
primes. This is the exact form usable uniformly over a
truncated compact prefix-product region. -/
theorem primeWindow_relative_from_PNT2
    (Y C z y ε : ℝ)
    (hz : 0 ≤ z) (hzy : z ≤ y) (hY : Y ≤ y)
    (hy : 1 < y) (hε : 0 ≤ ε)
    (hPNT2 : ∀ u : ℝ, Y ≤ u →
      |(Nat.primeCounting (Nat.floor u):ℝ) - u/Real.log u| ≤
        C*u/(Real.log u)^2)
    (hPNTbudget : C/Real.log y ≤ ε/2)
    (hsmallbudget : z+1 ≤ (ε/2)*(y/Real.log y)) :
    (1-ε)*(y/Real.log y) ≤ ((primeWindow z y).card : ℝ) := by
  have _ := hε
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hpos : 0 ≤ y/Real.log y :=
    div_nonneg (by linarith) hlog.le
  have hmul := mul_le_mul_of_nonneg_right hPNTbudget hpos
  have herr : C*y/(Real.log y)^2 ≤ (ε/2)*(y/Real.log y) := by
    calc
      C*y/(Real.log y)^2 =
          (C/Real.log y)*(y/Real.log y) := by
            field_simp
      _ ≤ _ := hmul
  have hbase := primeWindow_from_PNT2 Y C z y hz hzy hY hPNT2
  have htarget :
      (1-ε)*(y/Real.log y) ≤
        y/Real.log y - C*y/(Real.log y)^2 - (z+1) := by
    nlinarith
  exact htarget.trans hbase


/-- The prime-window Finset is exactly a real-boundary prime
interval. The lower endpoint is strict, the upper inclusive. -/
theorem mem_primeWindow_iff (z y : ℝ) (hz : 0 ≤ z)
    (hzy : z ≤ y) (p : ℕ) :
    p ∈ primeWindow z y ↔
      Nat.Prime p ∧ z < (p:ℝ) ∧ (p:ℝ) ≤ y := by
  simp only [primeWindow, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo,hhi⟩,hprime⟩
    refine ⟨hprime,?_,?_⟩
    · have hnat : (Nat.floor z + 1 : ℕ) ≤ p := by omega
      have hr : (Nat.floor z : ℝ) + 1 ≤ p := by exact_mod_cast hnat
      exact (Nat.lt_floor_add_one z).trans_le hr
    · have hr : (p:ℝ) ≤ (Nat.floor y : ℝ) := by exact_mod_cast hhi
      exact hr.trans (Nat.floor_le (hz.trans hzy))
  · rintro ⟨hprime,hlo,hhi⟩
    refine ⟨⟨?_,?_⟩,hprime⟩
    · have hl : (Nat.floor z:ℝ) < p :=
        (Nat.floor_le hz).trans_lt hlo
      exact_mod_cast hl
    · exact Nat.le_floor hhi

/-- The same actual-prime interval predicate without z≤y:
if the window is reversed, both sides are automatically empty. -/
theorem mem_primeWindow_iff_nonneg (z y : ℝ)
    (hz : 0 ≤ z) (hy : 0 ≤ y) (p : ℕ) :
    p ∈ primeWindow z y ↔
      Nat.Prime p ∧ z < (p:ℝ) ∧ (p:ℝ) ≤ y := by
  simp only [primeWindow, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo,hhi⟩,hprime⟩
    refine ⟨hprime,?_,?_⟩
    · have hnat : (Nat.floor z + 1 : ℕ) ≤ p := by omega
      have hr : (Nat.floor z : ℝ) + 1 ≤ p := by exact_mod_cast hnat
      exact (Nat.lt_floor_add_one z).trans_le hr
    · have hr : (p:ℝ) ≤ (Nat.floor y : ℝ) := by exact_mod_cast hhi
      exact hr.trans (Nat.floor_le hy)
  · rintro ⟨hprime,hlo,hhi⟩
    refine ⟨⟨?_,?_⟩,hprime⟩
    · have hl : (Nat.floor z:ℝ) < p :=
        (Nat.floor_le hz).trans_lt hlo
      exact_mod_cast hl
    · exact Nat.le_floor hhi

end Green64Analytic.OrderedPrimeRough

end

/-! ## LongPrimeAnalyticReduction -/

section

/- Task task-66d5aad32185. Each statement/proof has a pinned mathlib_verify receipt.
Named-module compilation is not performed in this worktree; see checks/index.json.
No assertion here is Green64.green_64. -/

namespace Green64Analytic.LongPrime

theorem khale_logderivative_strip :
let D : ℝ → ℝ → ℝ := fun Q v =>
  10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
    (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ)
(∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
  3 ≤ Q → 10 ≤ |s.im| → 1 - (D Q s.im)⁻¹ ≤ s.re →
  DirichletCharacter.LFunction χ s ≠ 0) →
∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Q V δ v K T L σ : ℝ),
let c : ℂ := (1+δ:ℝ) + (v:ℂ)*Complex.I
let f := DirichletCharacter.LFunction χ
3 * (q:ℝ) ≤ Q → 0 < δ → δ ≤ 1 → 20 ≤ |v| → |v| + 8*δ ≤ V →
100 * δ * D Q V ≤ 1 → 0 < K → 0 ≤ T → 0 < L → T ≤ δ*L →
(∀ w ∈ Metric.ball c (8*δ), Real.log ‖f w‖ ≤ K*(T+δ*L)) →
-K*T ≤ Real.log ‖f c‖ →
1-δ ≤ σ → σ ≤ 1+δ →
‖deriv f ((σ:ℂ)+v*Complex.I) / f ((σ:ℂ)+v*Complex.I)‖ ≤ 3*K*L
:= by
  have diskzero :
    let D : ℝ → ℝ → ℝ := fun Q v =>
      10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ)
    (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
      3 ≤ Q → 10 ≤ |s.im| → 1 - (D Q s.im)⁻¹ ≤ s.re →
      DirichletCharacter.LFunction χ s ≠ 0) →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Q V δ v : ℝ),
      3 * (q:ℝ) ≤ Q → 0 < δ → δ ≤ 1 → 20 ≤ |v| → |v| + 8*δ ≤ V →
      100 * δ * D Q V ≤ 1 →
    ∀ w ∈ Metric.closedBall ((1+δ:ℝ) + (v:ℂ) * Complex.I) (8*δ),
      DifferentiableAt ℂ (DirichletCharacter.LFunction χ) w ∧
      DirichletCharacter.LFunction χ w ≠ 0 := by
    have allmod : let width : ℝ → ℝ → ℝ := fun Q v =>
    (10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
      (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ))⁻¹
  (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
    3 ≤ Q → 10 ≤ |s.im| → 1 - width Q s.im ≤ s.re →
    DirichletCharacter.LFunction χ s ≠ 0) →
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    10 ≤ |s.im| → 1 - width (3 * q) s.im ≤ s.re →
    DirichletCharacter.LFunction χ s ≠ 0 := by
      intro width hKhale q hq χ s ht hs
      have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      have h3q : 3 ≤ 3 * q := by omega
      letI : NeZero (3 * q) := ⟨by omega⟩
      have hdiv : q ∣ 3 * q := dvd_mul_left q 3
      have hpole : s ≠ 1 := by
        intro he
        norm_num [he] at ht
      have hn := hKhale (3 * q) (DirichletCharacter.changeLevel hdiv χ) s h3q ht (by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs)
      rw [DirichletCharacter.LFunction_changeLevel hdiv χ (Or.inr hpole)] at hn
      exact (mul_ne_zero_iff.mp hn).1
    have denmono : let D : ℝ → ℝ → ℝ := fun Q v =>
    10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
      (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ)
  ∀ Q₁ Q₂ v V : ℝ, 3 ≤ Q₁ → Q₁ ≤ Q₂ → 10 ≤ |v| → |v| ≤ V →
  0 < D Q₁ v ∧ D Q₁ v ≤ D Q₂ V := by
      intro D Q₁ Q₂ v V hQ hQQ hv hvV
      have hQpos : 0 < Q₁ := by linarith
      have hvpos : 0 < |v| := by linarith
      have hVpos : 0 < V := lt_of_lt_of_le hvpos hvV
      have he : Real.exp 1 < |v| := by linarith [Real.exp_one_lt_d9]
      have hlogv : 1 < Real.log |v| := by
        have h := Real.log_lt_log (Real.exp_pos 1) he
        simpa using h
      have hlogV := Real.log_le_log hvpos hvV
      have hloglogv : 0 < Real.log (Real.log |v|) := Real.log_pos hlogv
      have hloglogV := Real.log_le_log (by linarith : 0 < Real.log |v|) hlogV
      have hlogQ : 0 < Real.log Q₁ := Real.log_pos (by linarith)
      have hlogQQ := Real.log_le_log hQpos hQQ
      have hpow₁ := Real.rpow_le_rpow (by linarith : 0 ≤ Real.log |v|) hlogV
        (by norm_num : (0:ℝ) ≤ 2/3)
      have hpow₂ := Real.rpow_le_rpow hloglogv.le hloglogV (by norm_num : (0:ℝ) ≤ 1/3)
      dsimp [D]
      rw [abs_of_pos hVpos]
      constructor
      · have hp₁ := Real.rpow_nonneg (by linarith : 0 ≤ Real.log |v|) (2/3:ℝ)
        have hp₂ := Real.rpow_nonneg hloglogv.le (1/3:ℝ)
        positivity
      · have hlogVpos : 0 ≤ Real.log V := by linarith
        gcongr <;> positivity
    intro D hKhale q _ χ Q V δ v hqQ hδ hδone hv hvV hbudget w hw
    have hall := allmod hKhale
    have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have hqreal : (1:ℝ) ≤ q := by exact_mod_cast hqpos
    have hn : ‖w - ((1+δ:ℝ) + (v:ℂ)*Complex.I)‖ ≤ 8*δ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
    have hi : |w.im-v| ≤ 8*δ := by
      simpa using (Complex.abs_im_le_norm (w - ((1+δ:ℝ) + (v:ℂ)*Complex.I))).trans hn
    have hr : |w.re-(1+δ)| ≤ 8*δ := by
      simpa using (Complex.abs_re_le_norm (w - ((1+δ:ℝ) + (v:ℂ)*Complex.I))).trans hn
    have habsdiff := abs_abs_sub_abs_le_abs_sub w.im v
    have hlower : 10 ≤ |w.im| := by
      have hh := (abs_le.mp (habsdiff.trans hi)).1
      linarith
    have hupper : |w.im| ≤ V := by
      have hh := (abs_le.mp (habsdiff.trans hi)).2
      linarith
    have hreal : 1-7*δ ≤ w.re := by have hh := (abs_le.mp hr).1; linarith
    have hD := denmono (3*(q:ℝ)) Q w.im V (by linarith) hqQ hlower hupper
    change 0 < D (3*(q:ℝ)) w.im ∧ D (3*(q:ℝ)) w.im ≤ D Q V at hD
    have hprod : 100*δ*D (3*(q:ℝ)) w.im ≤ 1 :=
      (mul_le_mul_of_nonneg_left hD.2 (by positivity)).trans hbudget
    have hwidth : 7*δ ≤ (D (3*(q:ℝ)) w.im)⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hD.1]
      nlinarith [mul_pos hδ hD.1]
    have hpole : w ≠ 1 := by intro he; norm_num [he] at hlower
    refine ⟨DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hpole), ?_⟩
    apply hall q χ w hlower
    change 1 - (D (3*(q:ℝ)) w.im)⁻¹ ≤ w.re
    linarith
  have logbound :
    ∀ (f : ℂ → ℂ) (c : ℂ) (δ B : ℝ), 0 < δ → 0 < B →
    DifferentiableOn ℂ f (Metric.ball c (8 * δ)) →
    (∀ w ∈ Metric.ball c (8 * δ), f w ≠ 0) →
    (∀ w ∈ Metric.ball c (8 * δ), Real.log ‖f w‖ - Real.log ‖f c‖ ≤ B) →
    ∀ z : ℂ, dist z c ≤ 2 * δ → ‖deriv f z / f z‖ ≤ B / δ := by
    have diskbound : ∀ (h : ℂ → ℂ) (c : ℂ) (δ B : ℝ), 0 < δ → 0 < B →
  DifferentiableOn ℂ h (Metric.ball c (8 * δ)) →
  (∀ w ∈ Metric.ball c (8 * δ), (h w - h c).re ≤ B) →
  ∀ z : ℂ, dist z c ≤ 2 * δ → ‖deriv h z‖ ≤ B / δ := by
      have half : ∀ (h : ℂ → ℂ) (c : ℂ) (δ B : ℝ), 0 < δ → 0 < B →
    DifferentiableOn ℂ h (Metric.ball c (8 * δ)) →
    (∀ w ∈ Metric.ball c (8 * δ), (h w - h c).re ≤ B) →
    ∀ w : ℂ, dist w c ≤ 4 * δ → ‖h w - h c‖ ≤ 2 * B := by
        intro h c δ B hδ hB hd hre w hw
        let f : ℂ → ℂ := fun z => h (z + c) - h c
        have hmap : Set.MapsTo (fun z : ℂ => z + c) (Metric.ball 0 (8*δ))
            (Metric.ball c (8*δ)) := by
          intro z hz
          simpa only [Metric.mem_ball, dist_eq_norm, sub_zero, add_sub_cancel_right] using hz
        have hf : DifferentiableOn ℂ f (Metric.ball 0 (8*δ)) :=
          (hd.comp (differentiableOn_id.add_const c) hmap).sub_const (h c)
        have hr : Set.MapsTo f (Metric.ball 0 (8*δ)) {z | z.re ≤ B} := by
          intro z hz
          exact hre (z+c) (hmap hz)
        have hz : w-c ∈ Metric.ball (0:ℂ) (8*δ) := by
          rw [Metric.mem_ball, dist_zero_right]
          rw [dist_eq_norm] at hw
          linarith
        have hb := Complex.borelCaratheodory_zero hB hf hr (by linarith) hz (by simp [f])
        have hn : ‖w-c‖ ≤ 4*δ := by simpa [dist_eq_norm] using hw
        have hden : 0 < 8*δ - ‖w-c‖ := by linarith
        have hq : 2*B*‖w-c‖ / (8*δ-‖w-c‖) ≤ 2*B := by
          apply (div_le_iff₀ hden).mpr
          nlinarith
        simpa [f] using hb.trans hq
      intro h c δ B hδ hB hd hre z hz
      have hsub : Metric.closedBall z (2*δ) ⊆ Metric.ball c (8*δ) := by
        intro w hw
        rw [Metric.mem_closedBall] at hw
        rw [Metric.mem_ball]
        have ht := dist_triangle w z c
        linarith
      have hd' : DiffContOnCl ℂ (fun w => h w - h c) (Metric.ball z (2*δ)) := by
        constructor
        · exact (hd.sub_const _).mono (Set.Subset.trans Metric.ball_subset_closedBall hsub)
        · exact (hd.sub_const _).continuousOn.mono
            ((closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans hsub)
      have hn : ∀ w ∈ Metric.sphere z (2*δ), ‖h w - h c‖ ≤ 2*B := by
        intro w hw
        apply half h c δ B hδ hB hd hre
        have he : dist w z = 2*δ := Metric.mem_sphere.mp hw
        calc dist w c ≤ dist w z + dist z c := dist_triangle w z c
             _ ≤ 4*δ := by linarith
      have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
        (by positivity : (0:ℝ) < 2*δ) hd' hn
      have hzmem : z ∈ Metric.ball c (8*δ) := by
        rw [Metric.mem_ball]; linarith
      have hdz := hd.differentiableAt (Metric.isOpen_ball.mem_nhds hzmem)
      rw [deriv_sub_const] at hb
      convert hb using 1 <;> field_simp <;> ring
    have branchderiv : ∀ (f h : ℂ → ℂ) (U : Set ℂ), IsOpen U →
  DifferentiableOn ℂ f U → ContinuousOn h U →
  Set.EqOn (Complex.exp ∘ h) f U →
  ∀ z ∈ U, HasDerivAt h (deriv f z / f z) z := by
      intro f h U hU hf hh heq z hz
      have hcont := hh.continuousAt (hU.mem_nhds hz)
      have hdiff := hf.differentiableAt (hU.mem_nhds hz)
      have he := Complex.hasStrictDerivAt_exp (h z)
      have hn := Complex.exp_ne_zero (h z)
      let g := he.localInverse Complex.exp (Complex.exp (h z)) (h z) hn
      have hgd : HasDerivAt g (Complex.exp (h z))⁻¹ (Complex.exp (h z)) :=
        (he.to_localInverse hn).hasDerivAt
      have hgz : Complex.exp (h z) = f z := heq hz
      have hcomp : HasDerivAt (fun w => g (f w)) (deriv f z / f z) z := by
        rw [hgz] at hgd
        simpa [div_eq_inv_mul, Function.comp_def] using! hgd.comp z hdiff.hasDerivAt
      have hleft : ∀ᶠ w in nhds z, g (Complex.exp (h w)) = h w :=
        hcont.eventually (he.eventually_left_inverse hn)
      have hevent : (fun w => g (f w)) =ᶠ[nhds z] h := by
        filter_upwards [hleft, hU.mem_nhds hz] with w hw hwU
        have hwf : Complex.exp (h w) = f w := heq hwU
        rw [hwf] at hw
        exact hw
      exact hcomp.congr_of_eventuallyEq hevent.symm
    intro f c δ B hδ hB hf hn hlog z hz
    have hne : (Metric.ball c (8*δ)).Nonempty := ⟨c, Metric.mem_ball_self (by positivity)⟩
    letI : ContractibleSpace (Metric.ball c (8*δ)) :=
      (convex_ball c (8*δ)).contractibleSpace hne
    have hsimp : IsSimplyConnected (Metric.ball c (8*δ)) := by
      change SimplyConnectedSpace (Metric.ball c (8*δ))
      infer_instance
    obtain ⟨h, hcont, heq⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsimp
      Metric.isOpen_ball hf.continuousOn (by
        rintro ⟨w, hw, he⟩
        exact hn w hw he)
    have hder := branchderiv f h (Metric.ball c (8*δ)) Metric.isOpen_ball hf hcont heq
    have hhd : DifferentiableOn ℂ h (Metric.ball c (8*δ)) := by
      intro w hw
      exact (hder w hw).differentiableAt.differentiableWithinAt
    have hre (w : ℂ) (hw : w ∈ Metric.ball c (8*δ)) : (h w).re = Real.log ‖f w‖ := by
      have he : Complex.exp (h w) = f w := heq hw
      rw [← he, Complex.norm_exp, Real.log_exp]
    have hc : c ∈ Metric.ball c (8*δ) := Metric.mem_ball_self (by positivity)
    have hb := diskbound h c δ B hδ hB hhd (by
      intro w hw
      rw [Complex.sub_re, hre w hw, hre c hc]
      exact hlog w hw) z hz
    have hzmem : z ∈ Metric.ball c (8*δ) := by rw [Metric.mem_ball]; linarith
    rw [(hder z hzmem).deriv] at hb
    exact hb
  intro D hKhale q _ χ Q V δ v K T L σ c f hqQ hδ hd1 hv hvV hbudget hK hT hL hTL hup hlo hσlo hσhi
  have hz := diskzero hKhale q χ Q V δ v hqQ hδ hd1 hv hvV hbudget
  have hf : DifferentiableOn ℂ f (Metric.ball c (8*δ)) := by
    intro w hw
    exact (hz w (Metric.ball_subset_closedBall hw)).1.differentiableWithinAt
  have hn : ∀ w ∈ Metric.ball c (8*δ), f w ≠ 0 := by
    intro w hw
    exact (hz w (Metric.ball_subset_closedBall hw)).2
  have hB : 0 < K*(2*T+δ*L) := by positivity
  have hdiff : ∀ w ∈ Metric.ball c (8*δ),
      Real.log ‖f w‖ - Real.log ‖f c‖ ≤ K*(2*T+δ*L) := by
    intro w hw
    have hu := hup w hw
    nlinarith
  have hdist : dist ((σ:ℂ)+v*Complex.I) c ≤ 2*δ := by
    rw [dist_eq_norm]
    have he : (σ:ℂ)+v*Complex.I-c = (σ-(1+δ):ℝ) := by dsimp [c]; push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hb := logbound f c δ (K*(2*T+δ*L)) hδ hB hf hn hdiff
    ((σ:ℂ)+v*Complex.I) hdist
  apply hb.trans
  apply (div_le_iff₀ hδ).mpr
  nlinarith [mul_le_mul_of_nonneg_left hTL hK.le]

theorem khale_logderivative_strip_nonzero :
let D : ℝ → ℝ → ℝ := fun Q v =>
  10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
    (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ)
(∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
  3 ≤ Q → 10 ≤ |s.im| → 1 - (D Q s.im)⁻¹ ≤ s.re →
  DirichletCharacter.LFunction χ s ≠ 0) →
∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Q V δ v K T L σ : ℝ),
let c : ℂ := (1+δ:ℝ) + (v:ℂ)*Complex.I
let f := DirichletCharacter.LFunction χ
3 * (q:ℝ) ≤ Q → 0 < δ → δ ≤ 1 → 20 ≤ |v| → |v| + 8*δ ≤ V →
100 * δ * D Q V ≤ 1 → 0 < K → 0 ≤ T → 0 < L → T ≤ δ*L →
(∀ w ∈ Metric.ball c (8*δ), Real.log ‖f w‖ ≤ K*(T+δ*L)) →
-K*T ≤ Real.log ‖f c‖ →
1-δ ≤ σ → σ ≤ 1+δ →
f ((σ:ℂ)+v*Complex.I) ≠ 0 ∧
‖deriv f ((σ:ℂ)+v*Complex.I) / f ((σ:ℂ)+v*Complex.I)‖ ≤ 3*K*L
:= by
  have diskzero :
    let D : ℝ → ℝ → ℝ := fun Q v =>
      10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ)
    (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
      3 ≤ Q → 10 ≤ |s.im| → 1 - (D Q s.im)⁻¹ ≤ s.re →
      DirichletCharacter.LFunction χ s ≠ 0) →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Q V δ v : ℝ),
      3 * (q:ℝ) ≤ Q → 0 < δ → δ ≤ 1 → 20 ≤ |v| → |v| + 8*δ ≤ V →
      100 * δ * D Q V ≤ 1 →
    ∀ w ∈ Metric.closedBall ((1+δ:ℝ) + (v:ℂ) * Complex.I) (8*δ),
      DifferentiableAt ℂ (DirichletCharacter.LFunction χ) w ∧
      DirichletCharacter.LFunction χ w ≠ 0 := by
    have allmod : let width : ℝ → ℝ → ℝ := fun Q v =>
    (10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
      (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ))⁻¹
  (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
    3 ≤ Q → 10 ≤ |s.im| → 1 - width Q s.im ≤ s.re →
    DirichletCharacter.LFunction χ s ≠ 0) →
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    10 ≤ |s.im| → 1 - width (3 * q) s.im ≤ s.re →
    DirichletCharacter.LFunction χ s ≠ 0 := by
      intro width hKhale q hq χ s ht hs
      have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      have h3q : 3 ≤ 3 * q := by omega
      letI : NeZero (3 * q) := ⟨by omega⟩
      have hdiv : q ∣ 3 * q := dvd_mul_left q 3
      have hpole : s ≠ 1 := by
        intro he
        norm_num [he] at ht
      have hn := hKhale (3 * q) (DirichletCharacter.changeLevel hdiv χ) s h3q ht (by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs)
      rw [DirichletCharacter.LFunction_changeLevel hdiv χ (Or.inr hpole)] at hn
      exact (mul_ne_zero_iff.mp hn).1
    have denmono : let D : ℝ → ℝ → ℝ := fun Q v =>
    10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
      (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ)
  ∀ Q₁ Q₂ v V : ℝ, 3 ≤ Q₁ → Q₁ ≤ Q₂ → 10 ≤ |v| → |v| ≤ V →
  0 < D Q₁ v ∧ D Q₁ v ≤ D Q₂ V := by
      intro D Q₁ Q₂ v V hQ hQQ hv hvV
      have hQpos : 0 < Q₁ := by linarith
      have hvpos : 0 < |v| := by linarith
      have hVpos : 0 < V := lt_of_lt_of_le hvpos hvV
      have he : Real.exp 1 < |v| := by linarith [Real.exp_one_lt_d9]
      have hlogv : 1 < Real.log |v| := by
        have h := Real.log_lt_log (Real.exp_pos 1) he
        simpa using h
      have hlogV := Real.log_le_log hvpos hvV
      have hloglogv : 0 < Real.log (Real.log |v|) := Real.log_pos hlogv
      have hloglogV := Real.log_le_log (by linarith : 0 < Real.log |v|) hlogV
      have hlogQ : 0 < Real.log Q₁ := Real.log_pos (by linarith)
      have hlogQQ := Real.log_le_log hQpos hQQ
      have hpow₁ := Real.rpow_le_rpow (by linarith : 0 ≤ Real.log |v|) hlogV
        (by norm_num : (0:ℝ) ≤ 2/3)
      have hpow₂ := Real.rpow_le_rpow hloglogv.le hloglogV (by norm_num : (0:ℝ) ≤ 1/3)
      dsimp [D]
      rw [abs_of_pos hVpos]
      constructor
      · have hp₁ := Real.rpow_nonneg (by linarith : 0 ≤ Real.log |v|) (2/3:ℝ)
        have hp₂ := Real.rpow_nonneg hloglogv.le (1/3:ℝ)
        positivity
      · have hlogVpos : 0 ≤ Real.log V := by linarith
        gcongr <;> positivity
    intro D hKhale q _ χ Q V δ v hqQ hδ hδone hv hvV hbudget w hw
    have hall := allmod hKhale
    have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have hqreal : (1:ℝ) ≤ q := by exact_mod_cast hqpos
    have hn : ‖w - ((1+δ:ℝ) + (v:ℂ)*Complex.I)‖ ≤ 8*δ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
    have hi : |w.im-v| ≤ 8*δ := by
      simpa using (Complex.abs_im_le_norm (w - ((1+δ:ℝ) + (v:ℂ)*Complex.I))).trans hn
    have hr : |w.re-(1+δ)| ≤ 8*δ := by
      simpa using (Complex.abs_re_le_norm (w - ((1+δ:ℝ) + (v:ℂ)*Complex.I))).trans hn
    have habsdiff := abs_abs_sub_abs_le_abs_sub w.im v
    have hlower : 10 ≤ |w.im| := by
      have hh := (abs_le.mp (habsdiff.trans hi)).1
      linarith
    have hupper : |w.im| ≤ V := by
      have hh := (abs_le.mp (habsdiff.trans hi)).2
      linarith
    have hreal : 1-7*δ ≤ w.re := by have hh := (abs_le.mp hr).1; linarith
    have hD := denmono (3*(q:ℝ)) Q w.im V (by linarith) hqQ hlower hupper
    change 0 < D (3*(q:ℝ)) w.im ∧ D (3*(q:ℝ)) w.im ≤ D Q V at hD
    have hprod : 100*δ*D (3*(q:ℝ)) w.im ≤ 1 :=
      (mul_le_mul_of_nonneg_left hD.2 (by positivity)).trans hbudget
    have hwidth : 7*δ ≤ (D (3*(q:ℝ)) w.im)⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hD.1]
      nlinarith [mul_pos hδ hD.1]
    have hpole : w ≠ 1 := by intro he; norm_num [he] at hlower
    refine ⟨DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hpole), ?_⟩
    apply hall q χ w hlower
    change 1 - (D (3*(q:ℝ)) w.im)⁻¹ ≤ w.re
    linarith
  have logbound :
    ∀ (f : ℂ → ℂ) (c : ℂ) (δ B : ℝ), 0 < δ → 0 < B →
    DifferentiableOn ℂ f (Metric.ball c (8 * δ)) →
    (∀ w ∈ Metric.ball c (8 * δ), f w ≠ 0) →
    (∀ w ∈ Metric.ball c (8 * δ), Real.log ‖f w‖ - Real.log ‖f c‖ ≤ B) →
    ∀ z : ℂ, dist z c ≤ 2 * δ → ‖deriv f z / f z‖ ≤ B / δ := by
    have diskbound : ∀ (h : ℂ → ℂ) (c : ℂ) (δ B : ℝ), 0 < δ → 0 < B →
  DifferentiableOn ℂ h (Metric.ball c (8 * δ)) →
  (∀ w ∈ Metric.ball c (8 * δ), (h w - h c).re ≤ B) →
  ∀ z : ℂ, dist z c ≤ 2 * δ → ‖deriv h z‖ ≤ B / δ := by
      have half : ∀ (h : ℂ → ℂ) (c : ℂ) (δ B : ℝ), 0 < δ → 0 < B →
    DifferentiableOn ℂ h (Metric.ball c (8 * δ)) →
    (∀ w ∈ Metric.ball c (8 * δ), (h w - h c).re ≤ B) →
    ∀ w : ℂ, dist w c ≤ 4 * δ → ‖h w - h c‖ ≤ 2 * B := by
        intro h c δ B hδ hB hd hre w hw
        let f : ℂ → ℂ := fun z => h (z + c) - h c
        have hmap : Set.MapsTo (fun z : ℂ => z + c) (Metric.ball 0 (8*δ))
            (Metric.ball c (8*δ)) := by
          intro z hz
          simpa only [Metric.mem_ball, dist_eq_norm, sub_zero, add_sub_cancel_right] using hz
        have hf : DifferentiableOn ℂ f (Metric.ball 0 (8*δ)) :=
          (hd.comp (differentiableOn_id.add_const c) hmap).sub_const (h c)
        have hr : Set.MapsTo f (Metric.ball 0 (8*δ)) {z | z.re ≤ B} := by
          intro z hz
          exact hre (z+c) (hmap hz)
        have hz : w-c ∈ Metric.ball (0:ℂ) (8*δ) := by
          rw [Metric.mem_ball, dist_zero_right]
          rw [dist_eq_norm] at hw
          linarith
        have hb := Complex.borelCaratheodory_zero hB hf hr (by linarith) hz (by simp [f])
        have hn : ‖w-c‖ ≤ 4*δ := by simpa [dist_eq_norm] using hw
        have hden : 0 < 8*δ - ‖w-c‖ := by linarith
        have hq : 2*B*‖w-c‖ / (8*δ-‖w-c‖) ≤ 2*B := by
          apply (div_le_iff₀ hden).mpr
          nlinarith
        simpa [f] using hb.trans hq
      intro h c δ B hδ hB hd hre z hz
      have hsub : Metric.closedBall z (2*δ) ⊆ Metric.ball c (8*δ) := by
        intro w hw
        rw [Metric.mem_closedBall] at hw
        rw [Metric.mem_ball]
        have ht := dist_triangle w z c
        linarith
      have hd' : DiffContOnCl ℂ (fun w => h w - h c) (Metric.ball z (2*δ)) := by
        constructor
        · exact (hd.sub_const _).mono (Set.Subset.trans Metric.ball_subset_closedBall hsub)
        · exact (hd.sub_const _).continuousOn.mono
            ((closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans hsub)
      have hn : ∀ w ∈ Metric.sphere z (2*δ), ‖h w - h c‖ ≤ 2*B := by
        intro w hw
        apply half h c δ B hδ hB hd hre
        have he : dist w z = 2*δ := Metric.mem_sphere.mp hw
        calc dist w c ≤ dist w z + dist z c := dist_triangle w z c
             _ ≤ 4*δ := by linarith
      have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
        (by positivity : (0:ℝ) < 2*δ) hd' hn
      have hzmem : z ∈ Metric.ball c (8*δ) := by
        rw [Metric.mem_ball]; linarith
      have hdz := hd.differentiableAt (Metric.isOpen_ball.mem_nhds hzmem)
      rw [deriv_sub_const] at hb
      convert hb using 1 <;> field_simp <;> ring
    have branchderiv : ∀ (f h : ℂ → ℂ) (U : Set ℂ), IsOpen U →
  DifferentiableOn ℂ f U → ContinuousOn h U →
  Set.EqOn (Complex.exp ∘ h) f U →
  ∀ z ∈ U, HasDerivAt h (deriv f z / f z) z := by
      intro f h U hU hf hh heq z hz
      have hcont := hh.continuousAt (hU.mem_nhds hz)
      have hdiff := hf.differentiableAt (hU.mem_nhds hz)
      have he := Complex.hasStrictDerivAt_exp (h z)
      have hn := Complex.exp_ne_zero (h z)
      let g := he.localInverse Complex.exp (Complex.exp (h z)) (h z) hn
      have hgd : HasDerivAt g (Complex.exp (h z))⁻¹ (Complex.exp (h z)) :=
        (he.to_localInverse hn).hasDerivAt
      have hgz : Complex.exp (h z) = f z := heq hz
      have hcomp : HasDerivAt (fun w => g (f w)) (deriv f z / f z) z := by
        rw [hgz] at hgd
        simpa [div_eq_inv_mul, Function.comp_def] using! hgd.comp z hdiff.hasDerivAt
      have hleft : ∀ᶠ w in nhds z, g (Complex.exp (h w)) = h w :=
        hcont.eventually (he.eventually_left_inverse hn)
      have hevent : (fun w => g (f w)) =ᶠ[nhds z] h := by
        filter_upwards [hleft, hU.mem_nhds hz] with w hw hwU
        have hwf : Complex.exp (h w) = f w := heq hwU
        rw [hwf] at hw
        exact hw
      exact hcomp.congr_of_eventuallyEq hevent.symm
    intro f c δ B hδ hB hf hn hlog z hz
    have hne : (Metric.ball c (8*δ)).Nonempty := ⟨c, Metric.mem_ball_self (by positivity)⟩
    letI : ContractibleSpace (Metric.ball c (8*δ)) :=
      (convex_ball c (8*δ)).contractibleSpace hne
    have hsimp : IsSimplyConnected (Metric.ball c (8*δ)) := by
      change SimplyConnectedSpace (Metric.ball c (8*δ))
      infer_instance
    obtain ⟨h, hcont, heq⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsimp
      Metric.isOpen_ball hf.continuousOn (by
        rintro ⟨w, hw, he⟩
        exact hn w hw he)
    have hder := branchderiv f h (Metric.ball c (8*δ)) Metric.isOpen_ball hf hcont heq
    have hhd : DifferentiableOn ℂ h (Metric.ball c (8*δ)) := by
      intro w hw
      exact (hder w hw).differentiableAt.differentiableWithinAt
    have hre (w : ℂ) (hw : w ∈ Metric.ball c (8*δ)) : (h w).re = Real.log ‖f w‖ := by
      have he : Complex.exp (h w) = f w := heq hw
      rw [← he, Complex.norm_exp, Real.log_exp]
    have hc : c ∈ Metric.ball c (8*δ) := Metric.mem_ball_self (by positivity)
    have hb := diskbound h c δ B hδ hB hhd (by
      intro w hw
      rw [Complex.sub_re, hre w hw, hre c hc]
      exact hlog w hw) z hz
    have hzmem : z ∈ Metric.ball c (8*δ) := by rw [Metric.mem_ball]; linarith
    rw [(hder z hzmem).deriv] at hb
    exact hb
  intro D hKhale q _ χ Q V δ v K T L σ c f hqQ hδ hd1 hv hvV hbudget hK hT hL hTL hup hlo hσlo hσhi
  have hz := diskzero hKhale q χ Q V δ v hqQ hδ hd1 hv hvV hbudget
  have hf : DifferentiableOn ℂ f (Metric.ball c (8*δ)) := by
    intro w hw
    exact (hz w (Metric.ball_subset_closedBall hw)).1.differentiableWithinAt
  have hn : ∀ w ∈ Metric.ball c (8*δ), f w ≠ 0 := by
    intro w hw
    exact (hz w (Metric.ball_subset_closedBall hw)).2
  have hB : 0 < K*(2*T+δ*L) := by positivity
  have hdiff : ∀ w ∈ Metric.ball c (8*δ),
      Real.log ‖f w‖ - Real.log ‖f c‖ ≤ K*(2*T+δ*L) := by
    intro w hw
    have hu := hup w hw
    nlinarith
  have hdist : dist ((σ:ℂ)+v*Complex.I) c ≤ 2*δ := by
    rw [dist_eq_norm]
    have he : (σ:ℂ)+v*Complex.I-c = (σ-(1+δ):ℝ) := by dsimp [c]; push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  constructor
  · exact (hz ((σ:ℂ)+v*Complex.I) (by
      rw [Metric.mem_closedBall]
      linarith)).2
  · have hb := logbound f c δ (K*(2*T+δ*L)) hδ hB hf hn hdiff
      ((σ:ℂ)+v*Complex.I) hdist
    apply hb.trans
    apply (div_le_iff₀ hδ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hTL hK.le]

theorem khale_truncated_mellin :
let D : ℝ → ℝ → ℝ := fun Q v =>
  10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
    (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ)
(∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
  3 ≤ Q → 10 ≤ |s.im| → 1 - (D Q s.im)⁻¹ ≤ s.re →
  DirichletCharacter.LFunction χ s ≠ 0) →
∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
  (N Q V δ a H t K T L Mv Mh : ℝ) (g : ℝ → ℂ),
let c : ℝ → ℂ := fun v => (1+δ:ℝ) + (v:ℂ)*Complex.I
let f := DirichletCharacter.LFunction χ
let F : ℂ → ℂ := fun z => mellin g z * (N:ℂ)^z *
  (-deriv f (1-(t:ℂ)*Complex.I+z) / f (1-(t:ℂ)*Complex.I+z))
1 ≤ N → 3*(q:ℝ) ≤ Q → 0 < δ → δ ≤ 1 → 0 ≤ a → a ≤ δ → 0 ≤ H →
20+H ≤ |t| → |t|+H+8*δ ≤ V → 100*δ*D Q V ≤ 1 →
0 < K → 0 ≤ T → 0 < L → T ≤ δ*L → 0 ≤ Mv → 0 ≤ Mh →
Continuous g → (∀ u : ℝ, u < 1/2 ∨ 3 < u → g u = 0) →
(∀ y ∈ Set.Icc (-H) H, ∀ w ∈ Metric.ball (c (y-t)) (8*δ),
  Real.log ‖f w‖ ≤ K*(T+δ*L)) →
(∀ y ∈ Set.Icc (-H) H, -K*T ≤ Real.log ‖f (c (y-t))‖) →
(∀ y ∈ Set.Icc (-H) H, ‖mellin g ((-δ:ℝ)+(y:ℂ)*Complex.I)‖ ≤ Mv) →
(∀ u ∈ Set.Icc (-δ) a, ‖mellin g ((u:ℂ)-H*Complex.I)‖ ≤ Mh ∧
  ‖mellin g ((u:ℂ)+H*Complex.I)‖ ≤ Mh) →
‖∫ y in (-H)..H, F ((a:ℂ)+y*Complex.I)‖ ≤
  2*H*(Mv*N^(-δ)*(3*K*L)) + 2*(a+δ)*(Mh*N^a*(3*K*L))
:= by
  have strip :
    let D : ℝ → ℝ → ℝ := fun Q v =>
      10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ)
    (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
      3 ≤ Q → 10 ≤ |s.im| → 1 - (D Q s.im)⁻¹ ≤ s.re →
      DirichletCharacter.LFunction χ s ≠ 0) →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Q V δ v K T L σ : ℝ),
    let c : ℂ := (1+δ:ℝ) + (v:ℂ)*Complex.I
    let f := DirichletCharacter.LFunction χ
    3 * (q:ℝ) ≤ Q → 0 < δ → δ ≤ 1 → 20 ≤ |v| → |v| + 8*δ ≤ V →
    100 * δ * D Q V ≤ 1 → 0 < K → 0 ≤ T → 0 < L → T ≤ δ*L →
    (∀ w ∈ Metric.ball c (8*δ), Real.log ‖f w‖ ≤ K*(T+δ*L)) →
    -K*T ≤ Real.log ‖f c‖ →
    1-δ ≤ σ → σ ≤ 1+δ →
    f ((σ:ℂ)+v*Complex.I) ≠ 0 ∧
    ‖deriv f ((σ:ℂ)+v*Complex.I) / f ((σ:ℂ)+v*Complex.I)‖ ≤ 3*K*L := by
    have diskzero :
      let D : ℝ → ℝ → ℝ := fun Q v =>
        10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ)
      (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
        3 ≤ Q → 10 ≤ |s.im| → 1 - (D Q s.im)⁻¹ ≤ s.re →
        DirichletCharacter.LFunction χ s ≠ 0) →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Q V δ v : ℝ),
        3 * (q:ℝ) ≤ Q → 0 < δ → δ ≤ 1 → 20 ≤ |v| → |v| + 8*δ ≤ V →
        100 * δ * D Q V ≤ 1 →
      ∀ w ∈ Metric.closedBall ((1+δ:ℝ) + (v:ℂ) * Complex.I) (8*δ),
        DifferentiableAt ℂ (DirichletCharacter.LFunction χ) w ∧
        DirichletCharacter.LFunction χ w ≠ 0 := by
      have allmod : let width : ℝ → ℝ → ℝ := fun Q v =>
      (10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ))⁻¹
    (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
      3 ≤ Q → 10 ≤ |s.im| → 1 - width Q s.im ≤ s.re →
      DirichletCharacter.LFunction χ s ≠ 0) →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      10 ≤ |s.im| → 1 - width (3 * q) s.im ≤ s.re →
      DirichletCharacter.LFunction χ s ≠ 0 := by
        intro width hKhale q hq χ s ht hs
        have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
        have h3q : 3 ≤ 3 * q := by omega
        letI : NeZero (3 * q) := ⟨by omega⟩
        have hdiv : q ∣ 3 * q := dvd_mul_left q 3
        have hpole : s ≠ 1 := by
          intro he
          norm_num [he] at ht
        have hn := hKhale (3 * q) (DirichletCharacter.changeLevel hdiv χ) s h3q ht (by
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs)
        rw [DirichletCharacter.LFunction_changeLevel hdiv χ (Or.inr hpole)] at hn
        exact (mul_ne_zero_iff.mp hn).1
      have denmono : let D : ℝ → ℝ → ℝ := fun Q v =>
      10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ)
    ∀ Q₁ Q₂ v V : ℝ, 3 ≤ Q₁ → Q₁ ≤ Q₂ → 10 ≤ |v| → |v| ≤ V →
    0 < D Q₁ v ∧ D Q₁ v ≤ D Q₂ V := by
        intro D Q₁ Q₂ v V hQ hQQ hv hvV
        have hQpos : 0 < Q₁ := by linarith
        have hvpos : 0 < |v| := by linarith
        have hVpos : 0 < V := lt_of_lt_of_le hvpos hvV
        have he : Real.exp 1 < |v| := by linarith [Real.exp_one_lt_d9]
        have hlogv : 1 < Real.log |v| := by
          have h := Real.log_lt_log (Real.exp_pos 1) he
          simpa using h
        have hlogV := Real.log_le_log hvpos hvV
        have hloglogv : 0 < Real.log (Real.log |v|) := Real.log_pos hlogv
        have hloglogV := Real.log_le_log (by linarith : 0 < Real.log |v|) hlogV
        have hlogQ : 0 < Real.log Q₁ := Real.log_pos (by linarith)
        have hlogQQ := Real.log_le_log hQpos hQQ
        have hpow₁ := Real.rpow_le_rpow (by linarith : 0 ≤ Real.log |v|) hlogV
          (by norm_num : (0:ℝ) ≤ 2/3)
        have hpow₂ := Real.rpow_le_rpow hloglogv.le hloglogV (by norm_num : (0:ℝ) ≤ 1/3)
        dsimp [D]
        rw [abs_of_pos hVpos]
        constructor
        · have hp₁ := Real.rpow_nonneg (by linarith : 0 ≤ Real.log |v|) (2/3:ℝ)
          have hp₂ := Real.rpow_nonneg hloglogv.le (1/3:ℝ)
          positivity
        · have hlogVpos : 0 ≤ Real.log V := by linarith
          gcongr <;> positivity
      intro D hKhale q _ χ Q V δ v hqQ hδ hδone hv hvV hbudget w hw
      have hall := allmod hKhale
      have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      have hqreal : (1:ℝ) ≤ q := by exact_mod_cast hqpos
      have hn : ‖w - ((1+δ:ℝ) + (v:ℂ)*Complex.I)‖ ≤ 8*δ := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
      have hi : |w.im-v| ≤ 8*δ := by
        simpa using (Complex.abs_im_le_norm (w - ((1+δ:ℝ) + (v:ℂ)*Complex.I))).trans hn
      have hr : |w.re-(1+δ)| ≤ 8*δ := by
        simpa using (Complex.abs_re_le_norm (w - ((1+δ:ℝ) + (v:ℂ)*Complex.I))).trans hn
      have habsdiff := abs_abs_sub_abs_le_abs_sub w.im v
      have hlower : 10 ≤ |w.im| := by
        have hh := (abs_le.mp (habsdiff.trans hi)).1
        linarith
      have hupper : |w.im| ≤ V := by
        have hh := (abs_le.mp (habsdiff.trans hi)).2
        linarith
      have hreal : 1-7*δ ≤ w.re := by have hh := (abs_le.mp hr).1; linarith
      have hD := denmono (3*(q:ℝ)) Q w.im V (by linarith) hqQ hlower hupper
      change 0 < D (3*(q:ℝ)) w.im ∧ D (3*(q:ℝ)) w.im ≤ D Q V at hD
      have hprod : 100*δ*D (3*(q:ℝ)) w.im ≤ 1 :=
        (mul_le_mul_of_nonneg_left hD.2 (by positivity)).trans hbudget
      have hwidth : 7*δ ≤ (D (3*(q:ℝ)) w.im)⁻¹ := by
        rw [inv_eq_one_div, le_div_iff₀ hD.1]
        nlinarith [mul_pos hδ hD.1]
      have hpole : w ≠ 1 := by intro he; norm_num [he] at hlower
      refine ⟨DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hpole), ?_⟩
      apply hall q χ w hlower
      change 1 - (D (3*(q:ℝ)) w.im)⁻¹ ≤ w.re
      linarith
    have logbound :
      ∀ (f : ℂ → ℂ) (c : ℂ) (δ B : ℝ), 0 < δ → 0 < B →
      DifferentiableOn ℂ f (Metric.ball c (8 * δ)) →
      (∀ w ∈ Metric.ball c (8 * δ), f w ≠ 0) →
      (∀ w ∈ Metric.ball c (8 * δ), Real.log ‖f w‖ - Real.log ‖f c‖ ≤ B) →
      ∀ z : ℂ, dist z c ≤ 2 * δ → ‖deriv f z / f z‖ ≤ B / δ := by
      have diskbound : ∀ (h : ℂ → ℂ) (c : ℂ) (δ B : ℝ), 0 < δ → 0 < B →
    DifferentiableOn ℂ h (Metric.ball c (8 * δ)) →
    (∀ w ∈ Metric.ball c (8 * δ), (h w - h c).re ≤ B) →
    ∀ z : ℂ, dist z c ≤ 2 * δ → ‖deriv h z‖ ≤ B / δ := by
        have half : ∀ (h : ℂ → ℂ) (c : ℂ) (δ B : ℝ), 0 < δ → 0 < B →
      DifferentiableOn ℂ h (Metric.ball c (8 * δ)) →
      (∀ w ∈ Metric.ball c (8 * δ), (h w - h c).re ≤ B) →
      ∀ w : ℂ, dist w c ≤ 4 * δ → ‖h w - h c‖ ≤ 2 * B := by
          intro h c δ B hδ hB hd hre w hw
          let f : ℂ → ℂ := fun z => h (z + c) - h c
          have hmap : Set.MapsTo (fun z : ℂ => z + c) (Metric.ball 0 (8*δ))
              (Metric.ball c (8*δ)) := by
            intro z hz
            simpa only [Metric.mem_ball, dist_eq_norm, sub_zero, add_sub_cancel_right] using hz
          have hf : DifferentiableOn ℂ f (Metric.ball 0 (8*δ)) :=
            (hd.comp (differentiableOn_id.add_const c) hmap).sub_const (h c)
          have hr : Set.MapsTo f (Metric.ball 0 (8*δ)) {z | z.re ≤ B} := by
            intro z hz
            exact hre (z+c) (hmap hz)
          have hz : w-c ∈ Metric.ball (0:ℂ) (8*δ) := by
            rw [Metric.mem_ball, dist_zero_right]
            rw [dist_eq_norm] at hw
            linarith
          have hb := Complex.borelCaratheodory_zero hB hf hr (by linarith) hz (by simp [f])
          have hn : ‖w-c‖ ≤ 4*δ := by simpa [dist_eq_norm] using hw
          have hden : 0 < 8*δ - ‖w-c‖ := by linarith
          have hq : 2*B*‖w-c‖ / (8*δ-‖w-c‖) ≤ 2*B := by
            apply (div_le_iff₀ hden).mpr
            nlinarith
          simpa [f] using hb.trans hq
        intro h c δ B hδ hB hd hre z hz
        have hsub : Metric.closedBall z (2*δ) ⊆ Metric.ball c (8*δ) := by
          intro w hw
          rw [Metric.mem_closedBall] at hw
          rw [Metric.mem_ball]
          have ht := dist_triangle w z c
          linarith
        have hd' : DiffContOnCl ℂ (fun w => h w - h c) (Metric.ball z (2*δ)) := by
          constructor
          · exact (hd.sub_const _).mono (Set.Subset.trans Metric.ball_subset_closedBall hsub)
          · exact (hd.sub_const _).continuousOn.mono
              ((closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans hsub)
        have hn : ∀ w ∈ Metric.sphere z (2*δ), ‖h w - h c‖ ≤ 2*B := by
          intro w hw
          apply half h c δ B hδ hB hd hre
          have he : dist w z = 2*δ := Metric.mem_sphere.mp hw
          calc dist w c ≤ dist w z + dist z c := dist_triangle w z c
               _ ≤ 4*δ := by linarith
        have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
          (by positivity : (0:ℝ) < 2*δ) hd' hn
        have hzmem : z ∈ Metric.ball c (8*δ) := by
          rw [Metric.mem_ball]; linarith
        have hdz := hd.differentiableAt (Metric.isOpen_ball.mem_nhds hzmem)
        rw [deriv_sub_const] at hb
        convert hb using 1 <;> field_simp <;> ring
      have branchderiv : ∀ (f h : ℂ → ℂ) (U : Set ℂ), IsOpen U →
    DifferentiableOn ℂ f U → ContinuousOn h U →
    Set.EqOn (Complex.exp ∘ h) f U →
    ∀ z ∈ U, HasDerivAt h (deriv f z / f z) z := by
        intro f h U hU hf hh heq z hz
        have hcont := hh.continuousAt (hU.mem_nhds hz)
        have hdiff := hf.differentiableAt (hU.mem_nhds hz)
        have he := Complex.hasStrictDerivAt_exp (h z)
        have hn := Complex.exp_ne_zero (h z)
        let g := he.localInverse Complex.exp (Complex.exp (h z)) (h z) hn
        have hgd : HasDerivAt g (Complex.exp (h z))⁻¹ (Complex.exp (h z)) :=
          (he.to_localInverse hn).hasDerivAt
        have hgz : Complex.exp (h z) = f z := heq hz
        have hcomp : HasDerivAt (fun w => g (f w)) (deriv f z / f z) z := by
          rw [hgz] at hgd
          simpa [div_eq_inv_mul, Function.comp_def] using! hgd.comp z hdiff.hasDerivAt
        have hleft : ∀ᶠ w in nhds z, g (Complex.exp (h w)) = h w :=
          hcont.eventually (he.eventually_left_inverse hn)
        have hevent : (fun w => g (f w)) =ᶠ[nhds z] h := by
          filter_upwards [hleft, hU.mem_nhds hz] with w hw hwU
          have hwf : Complex.exp (h w) = f w := heq hwU
          rw [hwf] at hw
          exact hw
        exact hcomp.congr_of_eventuallyEq hevent.symm
      intro f c δ B hδ hB hf hn hlog z hz
      have hne : (Metric.ball c (8*δ)).Nonempty := ⟨c, Metric.mem_ball_self (by positivity)⟩
      letI : ContractibleSpace (Metric.ball c (8*δ)) :=
        (convex_ball c (8*δ)).contractibleSpace hne
      have hsimp : IsSimplyConnected (Metric.ball c (8*δ)) := by
        change SimplyConnectedSpace (Metric.ball c (8*δ))
        infer_instance
      obtain ⟨h, hcont, heq⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsimp
        Metric.isOpen_ball hf.continuousOn (by
          rintro ⟨w, hw, he⟩
          exact hn w hw he)
      have hder := branchderiv f h (Metric.ball c (8*δ)) Metric.isOpen_ball hf hcont heq
      have hhd : DifferentiableOn ℂ h (Metric.ball c (8*δ)) := by
        intro w hw
        exact (hder w hw).differentiableAt.differentiableWithinAt
      have hre (w : ℂ) (hw : w ∈ Metric.ball c (8*δ)) : (h w).re = Real.log ‖f w‖ := by
        have he : Complex.exp (h w) = f w := heq hw
        rw [← he, Complex.norm_exp, Real.log_exp]
      have hc : c ∈ Metric.ball c (8*δ) := Metric.mem_ball_self (by positivity)
      have hb := diskbound h c δ B hδ hB hhd (by
        intro w hw
        rw [Complex.sub_re, hre w hw, hre c hc]
        exact hlog w hw) z hz
      have hzmem : z ∈ Metric.ball c (8*δ) := by rw [Metric.mem_ball]; linarith
      rw [(hder z hzmem).deriv] at hb
      exact hb
    intro D hKhale q _ χ Q V δ v K T L σ c f hqQ hδ hd1 hv hvV hbudget hK hT hL hTL hup hlo hσlo hσhi
    have hz := diskzero hKhale q χ Q V δ v hqQ hδ hd1 hv hvV hbudget
    have hf : DifferentiableOn ℂ f (Metric.ball c (8*δ)) := by
      intro w hw
      exact (hz w (Metric.ball_subset_closedBall hw)).1.differentiableWithinAt
    have hn : ∀ w ∈ Metric.ball c (8*δ), f w ≠ 0 := by
      intro w hw
      exact (hz w (Metric.ball_subset_closedBall hw)).2
    have hB : 0 < K*(2*T+δ*L) := by positivity
    have hdiff : ∀ w ∈ Metric.ball c (8*δ),
        Real.log ‖f w‖ - Real.log ‖f c‖ ≤ K*(2*T+δ*L) := by
      intro w hw
      have hu := hup w hw
      nlinarith
    have hdist : dist ((σ:ℂ)+v*Complex.I) c ≤ 2*δ := by
      rw [dist_eq_norm]
      have he : (σ:ℂ)+v*Complex.I-c = (σ-(1+δ):ℝ) := by dsimp [c]; push_cast; ring
      rw [he, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    constructor
    · exact (hz ((σ:ℂ)+v*Complex.I) (by
        rw [Metric.mem_closedBall]
        linarith)).2
    · have hb := logbound f c δ (K*(2*T+δ*L)) hδ hB hf hn hdiff
        ((σ:ℂ)+v*Complex.I) hdist
      apply hb.trans
      apply (div_le_iff₀ hδ).mpr
      nlinarith [mul_le_mul_of_nonneg_left hTL hK.le]
  have contour :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (N δ a H t K Mv Mh : ℝ) (g : ℝ → ℂ),
    let R := Complex.reProdIm (Set.Icc (-δ) a) (Set.Icc (-H) H)
    let S : ℂ → ℂ := fun z => 1 - (t:ℂ)*Complex.I + z
    let f := DirichletCharacter.LFunction χ
    let F : ℂ → ℂ := fun z => mellin g z * (N:ℂ)^z * (-deriv f (S z) / f (S z))
    1 ≤ N → 0 ≤ δ → 0 ≤ a → 0 ≤ H → H < |t| → 0 ≤ Mv → 0 ≤ Mh →
    Continuous g → (∀ u : ℝ, u < 1/2 ∨ 3 < u → g u = 0) →
    (∀ z ∈ R, f (S z) ≠ 0) →
    (∀ z ∈ R, ‖deriv f (S z) / f (S z)‖ ≤ K) →
    (∀ y ∈ Set.Icc (-H) H, ‖mellin g ((-δ:ℝ) + (y:ℂ)*Complex.I)‖ ≤ Mv) →
    (∀ u ∈ Set.Icc (-δ) a, ‖mellin g ((u:ℂ)-H*Complex.I)‖ ≤ Mh ∧
      ‖mellin g ((u:ℂ)+H*Complex.I)‖ ≤ Mh) →
    ‖∫ y in (-H)..H, F ((a:ℂ)+y*Complex.I)‖ ≤
      2*H*(Mv*N^(-δ)*K) + 2*(a+δ)*(Mh*N^a*K) := by
    have rect :
      ∀ (F : ℂ → ℂ) (a b H Mv Mh : ℝ), a ≤ b → 0 ≤ H →
      DifferentiableOn ℂ F (Complex.reProdIm (Set.Icc a b) (Set.Icc (-H) H)) →
      (∀ y ∈ Set.Icc (-H) H, ‖F ((a:ℂ) + y*Complex.I)‖ ≤ Mv) →
      (∀ u ∈ Set.Icc a b, ‖F ((u:ℂ) - H*Complex.I)‖ ≤ Mh ∧
        ‖F ((u:ℂ) + H*Complex.I)‖ ≤ Mh) →
      ‖∫ y in (-H)..H, F ((b:ℂ) + y*Complex.I)‖ ≤ 2*H*Mv + 2*(b-a)*Mh := by
      intro F a b H Mv Mh hab hH hd hv hh
      have he := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
        ((a:ℂ) - H*Complex.I) ((b:ℂ) + H*Complex.I) (by
          simpa [Set.uIcc_of_le hab, Set.uIcc_of_le (show -H ≤ H by linarith)] using hd)
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.sub_im,
        Complex.mul_im, mul_one, zero_add, zero_sub, Complex.add_re, add_zero,
        Complex.add_im, Complex.real_smul, smul_eq_mul, Complex.ofReal_neg, neg_mul,
        ← sub_eq_add_neg] at he
      have hid :
        (∫ y in (-H)..H, F ((b:ℂ) + y*Complex.I)) =
        (∫ y in (-H)..H, F ((a:ℂ) + y*Complex.I)) +
        Complex.I * ((∫ u in a..b, F ((u:ℂ) - H*Complex.I)) -
          (∫ u in a..b, F ((u:ℂ) + H*Complex.I))) := by
        have alg (bot top right left : ℂ)
            (hh : bot-top+Complex.I*right-Complex.I*left=0) :
            right = left+Complex.I*(bot-top) := by
          linear_combination (norm := (ring_nf; simp [Complex.I_sq])) -Complex.I * hh
        exact alg _ _ _ _ he
      have hvl : ‖∫ y in (-H)..H, F ((a:ℂ)+y*Complex.I)‖ ≤ Mv*|H - -H| := intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => hv y (by
        have hh' : y ∈ Set.Ioc (-H) H := by simpa only [Set.uIoc_of_le (show -H ≤ H by linarith)] using hy
        exact ⟨hh'.1.le, hh'.2⟩))
      have hlo : ‖∫ u in a..b, F ((u:ℂ)-H*Complex.I)‖ ≤ Mh*|b-a| := intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => (hh u (by
        have hh' : u ∈ Set.Ioc a b := by simpa only [Set.uIoc_of_le hab] using hu
        exact ⟨hh'.1.le, hh'.2⟩)).1)
      have hhi : ‖∫ u in a..b, F ((u:ℂ)+H*Complex.I)‖ ≤ Mh*|b-a| := intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => (hh u (by
        have hh' : u ∈ Set.Ioc a b := by simpa only [Set.uIoc_of_le hab] using hu
        exact ⟨hh'.1.le, hh'.2⟩)).2)
      rw [abs_of_nonneg (by linarith : 0 ≤ H - -H)] at hvl
      rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hlo hhi
      rw [hid]
      calc
        _ ≤ ‖∫ y in (-H)..H, F ((a:ℂ)+y*Complex.I)‖ +
          ‖Complex.I * ((∫ u in a..b, F ((u:ℂ)-H*Complex.I)) -
            (∫ u in a..b, F ((u:ℂ)+H*Complex.I)))‖ := norm_add_le _ _
        _ ≤ Mv*(H - -H) + (Mh*(b-a) + Mh*(b-a)) := by
          rw [norm_mul, Complex.norm_I, one_mul]
          exact add_le_add hvl ((norm_sub_le _ _).trans (add_le_add hlo hhi))
        _ = _ := by ring
    have holo :
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (N a b H t : ℝ)
        (G : ℂ → ℂ),
      let R := Complex.reProdIm (Set.Icc a b) (Set.Icc (-H) H)
      let S : ℂ → ℂ := fun z => 1 - (t:ℂ)*Complex.I + z
      let F : ℂ → ℂ := fun z => G z * (N:ℂ)^z *
        (-(deriv (DirichletCharacter.LFunction χ) (S z)) / DirichletCharacter.LFunction χ (S z))
      0 < N → H < |t| → DifferentiableOn ℂ G R →
      (∀ z ∈ R, DirichletCharacter.LFunction χ (S z) ≠ 0) →
      DifferentiableOn ℂ F R := by
      intro q _ χ N a b H t G R S F hN ht hG hn
      have hmap : Set.MapsTo S R ({1}ᶜ : Set ℂ) := by
        intro z hz
        change S z ≠ 1
        intro he
        have hi := congrArg Complex.im he
        simp [S] at hi
        have hz' : z.re ∈ Set.Icc a b ∧ z.im ∈ Set.Icc (-H) H := hz
        have habs : |t| ≤ H := abs_le.mpr ⟨by linarith [hz'.2.1], by linarith [hz'.2.2]⟩
        exact (not_le_of_gt ht) habs
      have hL : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
        intro z hz
        exact (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
      have hD := hL.deriv isOpen_compl_singleton
      have hS : DifferentiableOn ℂ S R := by dsimp [S]; fun_prop
      have hP : DifferentiableOn ℂ (fun z : ℂ => (N:ℂ)^z) R := by
        have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
        fun_prop (disch := aesop)
      exact (hG.mul hP).mul (((hD.comp hS hmap).neg).div (hL.comp hS hmap) hn)
    have mellinhol :
      ∀ g : ℝ → ℂ, Continuous g →
      (∀ u : ℝ, u < 1/2 ∨ 3 < u → g u = 0) →
      Differentiable ℂ (mellin g) := by
      intro g hg hs z
      have htop (a : ℝ) : Asymptotics.IsBigO Filter.atTop g (fun u : ℝ => u ^ (-a)) := by
        apply Asymptotics.isBigO_iff.mpr
        refine ⟨1, ?_⟩
        filter_upwards [Filter.eventually_gt_atTop (3:ℝ)] with u hu
        simp [hs u (Or.inr hu)]
      have hbot (b : ℝ) : Asymptotics.IsBigO (nhdsWithin (0:ℝ) (Set.Ioi 0)) g
          (fun u : ℝ => u ^ (-b)) := by
        apply Asymptotics.isBigO_iff.mpr
        refine ⟨1, ?_⟩
        have he : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0), u < 1/2 :=
          (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2)).filter_mono nhdsWithin_le_nhds
        filter_upwards [he] with u hu
        simp [hs u (Or.inl hu)]
      exact (mellin_hasDerivAt_of_isBigO_rpow
        (hg.locallyIntegrable.locallyIntegrableOn (Set.Ioi 0)) (htop (z.re+1)) (by linarith)
        (hbot (z.re-1)) (by linarith)).2.differentiableAt
    intro q _ χ N δ a H t K Mv Mh g R S f F hN hδ ha hH ht hMv hMh hg hsupport hn hK hv hh
    have hNp : 0 < N := by linarith
    have hab : -δ ≤ a := by linarith
    have hG := (mellinhol g hg hsupport).differentiableOn (s := R)
    have hF := holo q χ N (-δ) a H t (mellin g) hNp ht hG hn
    have hnorm (z : ℂ) : ‖F z‖ =
        ‖mellin g z‖ * N^z.re * ‖deriv f (S z) / f (S z)‖ := by
      simp only [F, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hNp, neg_div, norm_neg]
    have hv' : ∀ y ∈ Set.Icc (-H) H, ‖F ((-δ:ℝ)+(y:ℂ)*Complex.I)‖ ≤ Mv*N^(-δ)*K := by
      intro y hy
      have hm : ((-δ:ℝ)+(y:ℂ)*Complex.I) ∈ R := by
        change _ ∈ Set.Icc (-δ) a ∧ _ ∈ Set.Icc (-H) H
        simpa using (show (-δ) ∈ Set.Icc (-δ) a ∧ y ∈ Set.Icc (-H) H from ⟨⟨le_rfl, hab⟩, hy⟩)
      rw [hnorm]
      have hpow : (((-δ:ℝ)+(y:ℂ)*Complex.I):ℂ).re = -δ := by simp
      rw [hpow]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hv y hy) (Real.rpow_nonneg hNp.le _))
        (hK _ hm) (norm_nonneg _) (mul_nonneg hMv (Real.rpow_nonneg hNp.le _))
    have hh' : ∀ u ∈ Set.Icc (-δ) a, ‖F ((u:ℂ)-H*Complex.I)‖ ≤ Mh*N^a*K ∧
        ‖F ((u:ℂ)+H*Complex.I)‖ ≤ Mh*N^a*K := by
      intro u hu
      have bound (z : ℂ) (hz : z ∈ R) (hzr : z.re = u) (hzG : ‖mellin g z‖ ≤ Mh) :
          ‖F z‖ ≤ Mh*N^a*K := by
        rw [hnorm, hzr]
        have hp := Real.rpow_le_rpow_of_exponent_le hN hu.2
        exact mul_le_mul (mul_le_mul hzG hp (Real.rpow_nonneg hNp.le _) hMh)
          (hK z hz) (norm_nonneg _) (mul_nonneg hMh (Real.rpow_nonneg hNp.le _))
      constructor
      · apply bound ((u:ℂ)-H*Complex.I) ?_ (by simp) (hh u hu).1
        change _ ∈ Set.Icc (-δ) a ∧ _ ∈ Set.Icc (-H) H
        simpa using (show u ∈ Set.Icc (-δ) a ∧ (-H) ∈ Set.Icc (-H) H from ⟨hu, le_rfl, by linarith⟩)
      · apply bound ((u:ℂ)+H*Complex.I) ?_ (by simp) (hh u hu).2
        change _ ∈ Set.Icc (-δ) a ∧ _ ∈ Set.Icc (-H) H
        simpa using (show u ∈ Set.Icc (-δ) a ∧ H ∈ Set.Icc (-H) H from ⟨hu, by linarith, le_rfl⟩)
    simpa only [sub_neg_eq_add] using rect F (-δ) a H (Mv*N^(-δ)*K) (Mh*N^a*K)
      hab hH hF hv' hh'
  intro D hKhale q _ χ N Q V δ a H t K T L Mv Mh g c f F
    hN hq hδ hd1 ha had hH ht htV hbudget hK hT hL hTL hMv hMh hg hs hup hlo hv hh
  have ht' : H < |t| := by linarith
  have geom (y : ℝ) (hy : y ∈ Set.Icc (-H) H) :
      20 ≤ |y-t| ∧ |y-t|+8*δ ≤ V := by
    have hyabs : |y| ≤ H := abs_le.mpr hy
    have htriangle : |t| ≤ |y-t|+|y| := by
      calc
        |t| = |(t-y)+y| := by congr 1; ring
        _ ≤ |t-y|+|y| := abs_add_le _ _
        _ = |y-t|+|y| := by rw [abs_sub_comm t y]
    have hu : |y-t| ≤ |t|+H := by
      apply abs_le.mpr
      constructor
      · linarith only [hy.1, le_abs_self t]
      · linarith only [hy.2, neg_abs_le t]
    constructor <;> linarith
  let R := Complex.reProdIm (Set.Icc (-δ) a) (Set.Icc (-H) H)
  let S : ℂ → ℂ := fun z => 1-(t:ℂ)*Complex.I+z
  have hrewrite (z : ℂ) : S z =
      ((1+z.re:ℝ):ℂ) + ((z.im-t:ℝ):ℂ)*Complex.I := by
    apply Complex.ext <;> simp [S] <;> ring
  have hzprops (z : ℂ) (hz : z ∈ R) :
      f (S z) ≠ 0 ∧ ‖deriv f (S z) / f (S z)‖ ≤ 3*K*L := by
    have hxy : z.re ∈ Set.Icc (-δ) a ∧ z.im ∈ Set.Icc (-H) H := hz
    obtain ⟨hlow,hhigh⟩ := geom z.im hxy.2
    have hσlo : 1-δ ≤ 1+z.re := by linarith [hxy.1.1]
    have hσhi : 1+z.re ≤ 1+δ := by linarith [hxy.1.2]
    have hb := strip hKhale q χ Q V δ (z.im-t) K T L (1+z.re)
      hq hδ hd1 hlow hhigh hbudget hK hT hL hTL
      (hup z.im hxy.2) (hlo z.im hxy.2) hσlo hσhi
    simpa only [hrewrite] using hb
  exact contour q χ N δ a H t (3*K*L) Mv Mh g hN hδ.le ha hH ht' hMv hMh hg hs
    (fun z hz => (hzprops z hz).1) (fun z hz => (hzprops z hz).2) hv hh

theorem khale_truncated_mellin_lower_discharged :
∃ δ₀ : ℝ, 0 < δ₀ ∧
let D : ℝ → ℝ → ℝ := fun Q v =>
  10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
    (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ)
(∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
  3 ≤ Q → 10 ≤ |s.im| → 1 - (D Q s.im)⁻¹ ≤ s.re →
  DirichletCharacter.LFunction χ s ≠ 0) →
∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
  (N Q V δ a H t K T L Mv Mh : ℝ) (g : ℝ → ℂ),
let c : ℝ → ℂ := fun v => (1+δ:ℝ) + (v:ℂ)*Complex.I
let f := DirichletCharacter.LFunction χ
let F : ℂ → ℂ := fun z => mellin g z * (N:ℂ)^z *
  (-deriv f (1-(t:ℂ)*Complex.I+z) / f (1-(t:ℂ)*Complex.I+z))
1 ≤ N → 3*(q:ℝ) ≤ Q → 0 < δ → δ < δ₀ → δ ≤ 1 → 0 ≤ a → a ≤ δ → 0 ≤ H →
20+H ≤ |t| → |t|+H+8*δ ≤ V → 100*δ*D Q V ≤ 1 →
0 < K → 0 ≤ T → 0 < L → T ≤ δ*L → 0 ≤ Mv → 0 ≤ Mh →
Continuous g → (∀ u : ℝ, u < 1/2 ∨ 3 < u → g u = 0) →
(∀ y ∈ Set.Icc (-H) H, ∀ w ∈ Metric.ball (c (y-t)) (8*δ),
  Real.log ‖f w‖ ≤ K*(T+δ*L)) →
-K*T ≤ Real.log δ - Real.log 2 →
(∀ y ∈ Set.Icc (-H) H, ‖mellin g ((-δ:ℝ)+(y:ℂ)*Complex.I)‖ ≤ Mv) →
(∀ u ∈ Set.Icc (-δ) a, ‖mellin g ((u:ℂ)-H*Complex.I)‖ ≤ Mh ∧
  ‖mellin g ((u:ℂ)+H*Complex.I)‖ ≤ Mh) →
‖∫ y in (-H)..H, F ((a:ℂ)+y*Complex.I)‖ ≤
  2*H*(Mv*N^(-δ)*(3*K*L)) + 2*(a+δ)*(Mh*N^a*(3*K*L))
:= by
  have center :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ (δ : ℝ), 0 < δ → δ < δ₀ →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (v : ℝ),
    δ/2 ≤ ‖DirichletCharacter.LFunction χ ((1+δ:ℝ) + (v:ℂ)*Complex.I)‖ ∧
    Real.log δ - Real.log 2 ≤
      Real.log ‖DirichletCharacter.LFunction χ ((1+δ:ℝ) + (v:ℂ)*Complex.I)‖ := by
    have recip :
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      1 < s.re →
      1 ≤ ‖DirichletCharacter.LFunction χ s‖ *
        (∑' n : ℕ, 1 / (n:ℝ)^s.re) := by
      intro q _ χ s hs
      let b : ℕ → ℂ := fun n => χ n * (ArithmeticFunction.moebius n : ℂ)
      have hb : LSeriesSummable b s := by
        exact χ.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
      have hprod : DirichletCharacter.LFunction χ s * LSeries b s = 1 := by
        rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
        exact DirichletCharacter.LSeries.mul_mu_eq_one χ hs
      have hsum : Summable (fun n : ℕ => 1/(n:ℝ)^s.re) := by
        exact Real.summable_one_div_nat_rpow.mpr hs
      have hterm (n : ℕ) : ‖LSeries.term b s n‖ ≤ 1/(n:ℝ)^s.re := by
        rw [LSeries.norm_term_eq]
        by_cases hn : n = 0
        · simp [hn, Real.zero_rpow (by linarith : s.re ≠ 0)]
        · rw [if_neg hn]
          apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
            norm_cast
            exact ArithmeticFunction.abs_moebius_le_one
          dsimp [b]
          rw [norm_mul]
          exact mul_le_one₀ (χ.norm_le_one n) (norm_nonneg _) hμ
      have hbound : ‖LSeries b s‖ ≤ ∑' n : ℕ, 1/(n:ℝ)^s.re :=
        (norm_tsum_le_tsum_norm hb.norm).trans (Summable.tsum_le_tsum hterm hb.norm hsum)
      have hh := congrArg norm hprod
      rw [norm_mul, norm_one] at hh
      calc
        1 = ‖DirichletCharacter.LFunction χ s‖ * ‖LSeries b s‖ := hh.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    have he : ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1),
        (s-1)*(∑' n : ℕ, 1/(n:ℝ)^s) < 2 :=
      tendsto_sub_mul_tsum_nat_rpow.eventually_lt_const (by norm_num)
    obtain ⟨ε,hε,hmem⟩ := Metric.mem_nhdsWithin_iff.mp he
    refine ⟨ε,hε,?_⟩
    intro δ hδ hδε q _ χ v
    have hm : (1+δ:ℝ) ∈ Metric.ball 1 ε ∩ Set.Ioi 1 := by
      constructor
      · simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hδ] using hδε
      · change 1 < 1+δ
        linarith
    have hs : δ*(∑' n : ℕ, 1/(n:ℝ)^(1+δ)) < 2 := by
      simpa using hmem hm
    let Z := ∑' n : ℕ, 1/(n:ℝ)^(1+δ)
    let c : ℂ := (1+δ:ℝ)+(v:ℂ)*Complex.I
    have hc : 1 < c.re := by dsimp [c]; simp only [Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; linarith
    have hrec : 1 ≤ ‖DirichletCharacter.LFunction χ c‖*Z := by
      simpa [c,Z] using recip q χ c hc
    have hnorm := norm_nonneg (DirichletCharacter.LFunction χ c)
    have h1 := mul_le_mul_of_nonneg_left hrec hδ.le
    have h2 := mul_le_mul_of_nonneg_left hs.le hnorm
    have hlow : δ/2 ≤ ‖DirichletCharacter.LFunction χ c‖ := by
      dsimp [Z] at h1 hrec h2 ⊢
      nlinarith
    refine ⟨hlow, ?_⟩
    have hlog := Real.log_le_log (by positivity : 0 < δ/2) hlow
    simpa only [Real.log_div hδ.ne' (by norm_num : (2:ℝ) ≠ 0)] using hlog
  have reduction :
    let D : ℝ → ℝ → ℝ := fun Q v =>
      10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ)
    (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
      3 ≤ Q → 10 ≤ |s.im| → 1 - (D Q s.im)⁻¹ ≤ s.re →
      DirichletCharacter.LFunction χ s ≠ 0) →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (N Q V δ a H t K T L Mv Mh : ℝ) (g : ℝ → ℂ),
    let c : ℝ → ℂ := fun v => (1+δ:ℝ) + (v:ℂ)*Complex.I
    let f := DirichletCharacter.LFunction χ
    let F : ℂ → ℂ := fun z => mellin g z * (N:ℂ)^z *
      (-deriv f (1-(t:ℂ)*Complex.I+z) / f (1-(t:ℂ)*Complex.I+z))
    1 ≤ N → 3*(q:ℝ) ≤ Q → 0 < δ → δ ≤ 1 → 0 ≤ a → a ≤ δ → 0 ≤ H →
    20+H ≤ |t| → |t|+H+8*δ ≤ V → 100*δ*D Q V ≤ 1 →
    0 < K → 0 ≤ T → 0 < L → T ≤ δ*L → 0 ≤ Mv → 0 ≤ Mh →
    Continuous g → (∀ u : ℝ, u < 1/2 ∨ 3 < u → g u = 0) →
    (∀ y ∈ Set.Icc (-H) H, ∀ w ∈ Metric.ball (c (y-t)) (8*δ),
      Real.log ‖f w‖ ≤ K*(T+δ*L)) →
    (∀ y ∈ Set.Icc (-H) H, -K*T ≤ Real.log ‖f (c (y-t))‖) →
    (∀ y ∈ Set.Icc (-H) H, ‖mellin g ((-δ:ℝ)+(y:ℂ)*Complex.I)‖ ≤ Mv) →
    (∀ u ∈ Set.Icc (-δ) a, ‖mellin g ((u:ℂ)-H*Complex.I)‖ ≤ Mh ∧
      ‖mellin g ((u:ℂ)+H*Complex.I)‖ ≤ Mh) →
    ‖∫ y in (-H)..H, F ((a:ℂ)+y*Complex.I)‖ ≤
      2*H*(Mv*N^(-δ)*(3*K*L)) + 2*(a+δ)*(Mh*N^a*(3*K*L)) := by
    have strip :
      let D : ℝ → ℝ → ℝ := fun Q v =>
        10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ)
      (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
        3 ≤ Q → 10 ≤ |s.im| → 1 - (D Q s.im)⁻¹ ≤ s.re →
        DirichletCharacter.LFunction χ s ≠ 0) →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Q V δ v K T L σ : ℝ),
      let c : ℂ := (1+δ:ℝ) + (v:ℂ)*Complex.I
      let f := DirichletCharacter.LFunction χ
      3 * (q:ℝ) ≤ Q → 0 < δ → δ ≤ 1 → 20 ≤ |v| → |v| + 8*δ ≤ V →
      100 * δ * D Q V ≤ 1 → 0 < K → 0 ≤ T → 0 < L → T ≤ δ*L →
      (∀ w ∈ Metric.ball c (8*δ), Real.log ‖f w‖ ≤ K*(T+δ*L)) →
      -K*T ≤ Real.log ‖f c‖ →
      1-δ ≤ σ → σ ≤ 1+δ →
      f ((σ:ℂ)+v*Complex.I) ≠ 0 ∧
      ‖deriv f ((σ:ℂ)+v*Complex.I) / f ((σ:ℂ)+v*Complex.I)‖ ≤ 3*K*L := by
      have diskzero :
        let D : ℝ → ℝ → ℝ := fun Q v =>
          10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ)
        (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
          3 ≤ Q → 10 ≤ |s.im| → 1 - (D Q s.im)⁻¹ ≤ s.re →
          DirichletCharacter.LFunction χ s ≠ 0) →
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Q V δ v : ℝ),
          3 * (q:ℝ) ≤ Q → 0 < δ → δ ≤ 1 → 20 ≤ |v| → |v| + 8*δ ≤ V →
          100 * δ * D Q V ≤ 1 →
        ∀ w ∈ Metric.closedBall ((1+δ:ℝ) + (v:ℂ) * Complex.I) (8*δ),
          DifferentiableAt ℂ (DirichletCharacter.LFunction χ) w ∧
          DirichletCharacter.LFunction χ w ≠ 0 := by
        have allmod : let width : ℝ → ℝ → ℝ := fun Q v =>
        (10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ))⁻¹
      (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
        3 ≤ Q → 10 ≤ |s.im| → 1 - width Q s.im ≤ s.re →
        DirichletCharacter.LFunction χ s ≠ 0) →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
        10 ≤ |s.im| → 1 - width (3 * q) s.im ≤ s.re →
        DirichletCharacter.LFunction χ s ≠ 0 := by
          intro width hKhale q hq χ s ht hs
          have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
          have h3q : 3 ≤ 3 * q := by omega
          letI : NeZero (3 * q) := ⟨by omega⟩
          have hdiv : q ∣ 3 * q := dvd_mul_left q 3
          have hpole : s ≠ 1 := by
            intro he
            norm_num [he] at ht
          have hn := hKhale (3 * q) (DirichletCharacter.changeLevel hdiv χ) s h3q ht (by
            simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs)
          rw [DirichletCharacter.LFunction_changeLevel hdiv χ (Or.inr hpole)] at hn
          exact (mul_ne_zero_iff.mp hn).1
        have denmono : let D : ℝ → ℝ → ℝ := fun Q v =>
        10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |v|)) ^ (1 / 3 : ℝ)
      ∀ Q₁ Q₂ v V : ℝ, 3 ≤ Q₁ → Q₁ ≤ Q₂ → 10 ≤ |v| → |v| ≤ V →
      0 < D Q₁ v ∧ D Q₁ v ≤ D Q₂ V := by
          intro D Q₁ Q₂ v V hQ hQQ hv hvV
          have hQpos : 0 < Q₁ := by linarith
          have hvpos : 0 < |v| := by linarith
          have hVpos : 0 < V := lt_of_lt_of_le hvpos hvV
          have he : Real.exp 1 < |v| := by linarith [Real.exp_one_lt_d9]
          have hlogv : 1 < Real.log |v| := by
            have h := Real.log_lt_log (Real.exp_pos 1) he
            simpa using h
          have hlogV := Real.log_le_log hvpos hvV
          have hloglogv : 0 < Real.log (Real.log |v|) := Real.log_pos hlogv
          have hloglogV := Real.log_le_log (by linarith : 0 < Real.log |v|) hlogV
          have hlogQ : 0 < Real.log Q₁ := Real.log_pos (by linarith)
          have hlogQQ := Real.log_le_log hQpos hQQ
          have hpow₁ := Real.rpow_le_rpow (by linarith : 0 ≤ Real.log |v|) hlogV
            (by norm_num : (0:ℝ) ≤ 2/3)
          have hpow₂ := Real.rpow_le_rpow hloglogv.le hloglogV (by norm_num : (0:ℝ) ≤ 1/3)
          dsimp [D]
          rw [abs_of_pos hVpos]
          constructor
          · have hp₁ := Real.rpow_nonneg (by linarith : 0 ≤ Real.log |v|) (2/3:ℝ)
            have hp₂ := Real.rpow_nonneg hloglogv.le (1/3:ℝ)
            positivity
          · have hlogVpos : 0 ≤ Real.log V := by linarith
            gcongr <;> positivity
        intro D hKhale q _ χ Q V δ v hqQ hδ hδone hv hvV hbudget w hw
        have hall := allmod hKhale
        have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
        have hqreal : (1:ℝ) ≤ q := by exact_mod_cast hqpos
        have hn : ‖w - ((1+δ:ℝ) + (v:ℂ)*Complex.I)‖ ≤ 8*δ := by
          simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
        have hi : |w.im-v| ≤ 8*δ := by
          simpa using (Complex.abs_im_le_norm (w - ((1+δ:ℝ) + (v:ℂ)*Complex.I))).trans hn
        have hr : |w.re-(1+δ)| ≤ 8*δ := by
          simpa using (Complex.abs_re_le_norm (w - ((1+δ:ℝ) + (v:ℂ)*Complex.I))).trans hn
        have habsdiff := abs_abs_sub_abs_le_abs_sub w.im v
        have hlower : 10 ≤ |w.im| := by
          have hh := (abs_le.mp (habsdiff.trans hi)).1
          linarith
        have hupper : |w.im| ≤ V := by
          have hh := (abs_le.mp (habsdiff.trans hi)).2
          linarith
        have hreal : 1-7*δ ≤ w.re := by have hh := (abs_le.mp hr).1; linarith
        have hD := denmono (3*(q:ℝ)) Q w.im V (by linarith) hqQ hlower hupper
        change 0 < D (3*(q:ℝ)) w.im ∧ D (3*(q:ℝ)) w.im ≤ D Q V at hD
        have hprod : 100*δ*D (3*(q:ℝ)) w.im ≤ 1 :=
          (mul_le_mul_of_nonneg_left hD.2 (by positivity)).trans hbudget
        have hwidth : 7*δ ≤ (D (3*(q:ℝ)) w.im)⁻¹ := by
          rw [inv_eq_one_div, le_div_iff₀ hD.1]
          nlinarith [mul_pos hδ hD.1]
        have hpole : w ≠ 1 := by intro he; norm_num [he] at hlower
        refine ⟨DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hpole), ?_⟩
        apply hall q χ w hlower
        change 1 - (D (3*(q:ℝ)) w.im)⁻¹ ≤ w.re
        linarith
      have logbound :
        ∀ (f : ℂ → ℂ) (c : ℂ) (δ B : ℝ), 0 < δ → 0 < B →
        DifferentiableOn ℂ f (Metric.ball c (8 * δ)) →
        (∀ w ∈ Metric.ball c (8 * δ), f w ≠ 0) →
        (∀ w ∈ Metric.ball c (8 * δ), Real.log ‖f w‖ - Real.log ‖f c‖ ≤ B) →
        ∀ z : ℂ, dist z c ≤ 2 * δ → ‖deriv f z / f z‖ ≤ B / δ := by
        have diskbound : ∀ (h : ℂ → ℂ) (c : ℂ) (δ B : ℝ), 0 < δ → 0 < B →
      DifferentiableOn ℂ h (Metric.ball c (8 * δ)) →
      (∀ w ∈ Metric.ball c (8 * δ), (h w - h c).re ≤ B) →
      ∀ z : ℂ, dist z c ≤ 2 * δ → ‖deriv h z‖ ≤ B / δ := by
          have half : ∀ (h : ℂ → ℂ) (c : ℂ) (δ B : ℝ), 0 < δ → 0 < B →
        DifferentiableOn ℂ h (Metric.ball c (8 * δ)) →
        (∀ w ∈ Metric.ball c (8 * δ), (h w - h c).re ≤ B) →
        ∀ w : ℂ, dist w c ≤ 4 * δ → ‖h w - h c‖ ≤ 2 * B := by
            intro h c δ B hδ hB hd hre w hw
            let f : ℂ → ℂ := fun z => h (z + c) - h c
            have hmap : Set.MapsTo (fun z : ℂ => z + c) (Metric.ball 0 (8*δ))
                (Metric.ball c (8*δ)) := by
              intro z hz
              simpa only [Metric.mem_ball, dist_eq_norm, sub_zero, add_sub_cancel_right] using hz
            have hf : DifferentiableOn ℂ f (Metric.ball 0 (8*δ)) :=
              (hd.comp (differentiableOn_id.add_const c) hmap).sub_const (h c)
            have hr : Set.MapsTo f (Metric.ball 0 (8*δ)) {z | z.re ≤ B} := by
              intro z hz
              exact hre (z+c) (hmap hz)
            have hz : w-c ∈ Metric.ball (0:ℂ) (8*δ) := by
              rw [Metric.mem_ball, dist_zero_right]
              rw [dist_eq_norm] at hw
              linarith
            have hb := Complex.borelCaratheodory_zero hB hf hr (by linarith) hz (by simp [f])
            have hn : ‖w-c‖ ≤ 4*δ := by simpa [dist_eq_norm] using hw
            have hden : 0 < 8*δ - ‖w-c‖ := by linarith
            have hq : 2*B*‖w-c‖ / (8*δ-‖w-c‖) ≤ 2*B := by
              apply (div_le_iff₀ hden).mpr
              nlinarith
            simpa [f] using hb.trans hq
          intro h c δ B hδ hB hd hre z hz
          have hsub : Metric.closedBall z (2*δ) ⊆ Metric.ball c (8*δ) := by
            intro w hw
            rw [Metric.mem_closedBall] at hw
            rw [Metric.mem_ball]
            have ht := dist_triangle w z c
            linarith
          have hd' : DiffContOnCl ℂ (fun w => h w - h c) (Metric.ball z (2*δ)) := by
            constructor
            · exact (hd.sub_const _).mono (Set.Subset.trans Metric.ball_subset_closedBall hsub)
            · exact (hd.sub_const _).continuousOn.mono
                ((closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans hsub)
          have hn : ∀ w ∈ Metric.sphere z (2*δ), ‖h w - h c‖ ≤ 2*B := by
            intro w hw
            apply half h c δ B hδ hB hd hre
            have he : dist w z = 2*δ := Metric.mem_sphere.mp hw
            calc dist w c ≤ dist w z + dist z c := dist_triangle w z c
                 _ ≤ 4*δ := by linarith
          have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
            (by positivity : (0:ℝ) < 2*δ) hd' hn
          have hzmem : z ∈ Metric.ball c (8*δ) := by
            rw [Metric.mem_ball]; linarith
          have hdz := hd.differentiableAt (Metric.isOpen_ball.mem_nhds hzmem)
          rw [deriv_sub_const] at hb
          convert hb using 1 <;> field_simp <;> ring
        have branchderiv : ∀ (f h : ℂ → ℂ) (U : Set ℂ), IsOpen U →
      DifferentiableOn ℂ f U → ContinuousOn h U →
      Set.EqOn (Complex.exp ∘ h) f U →
      ∀ z ∈ U, HasDerivAt h (deriv f z / f z) z := by
          intro f h U hU hf hh heq z hz
          have hcont := hh.continuousAt (hU.mem_nhds hz)
          have hdiff := hf.differentiableAt (hU.mem_nhds hz)
          have he := Complex.hasStrictDerivAt_exp (h z)
          have hn := Complex.exp_ne_zero (h z)
          let g := he.localInverse Complex.exp (Complex.exp (h z)) (h z) hn
          have hgd : HasDerivAt g (Complex.exp (h z))⁻¹ (Complex.exp (h z)) :=
            (he.to_localInverse hn).hasDerivAt
          have hgz : Complex.exp (h z) = f z := heq hz
          have hcomp : HasDerivAt (fun w => g (f w)) (deriv f z / f z) z := by
            rw [hgz] at hgd
            simpa [div_eq_inv_mul, Function.comp_def] using! hgd.comp z hdiff.hasDerivAt
          have hleft : ∀ᶠ w in nhds z, g (Complex.exp (h w)) = h w :=
            hcont.eventually (he.eventually_left_inverse hn)
          have hevent : (fun w => g (f w)) =ᶠ[nhds z] h := by
            filter_upwards [hleft, hU.mem_nhds hz] with w hw hwU
            have hwf : Complex.exp (h w) = f w := heq hwU
            rw [hwf] at hw
            exact hw
          exact hcomp.congr_of_eventuallyEq hevent.symm
        intro f c δ B hδ hB hf hn hlog z hz
        have hne : (Metric.ball c (8*δ)).Nonempty := ⟨c, Metric.mem_ball_self (by positivity)⟩
        letI : ContractibleSpace (Metric.ball c (8*δ)) :=
          (convex_ball c (8*δ)).contractibleSpace hne
        have hsimp : IsSimplyConnected (Metric.ball c (8*δ)) := by
          change SimplyConnectedSpace (Metric.ball c (8*δ))
          infer_instance
        obtain ⟨h, hcont, heq⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsimp
          Metric.isOpen_ball hf.continuousOn (by
            rintro ⟨w, hw, he⟩
            exact hn w hw he)
        have hder := branchderiv f h (Metric.ball c (8*δ)) Metric.isOpen_ball hf hcont heq
        have hhd : DifferentiableOn ℂ h (Metric.ball c (8*δ)) := by
          intro w hw
          exact (hder w hw).differentiableAt.differentiableWithinAt
        have hre (w : ℂ) (hw : w ∈ Metric.ball c (8*δ)) : (h w).re = Real.log ‖f w‖ := by
          have he : Complex.exp (h w) = f w := heq hw
          rw [← he, Complex.norm_exp, Real.log_exp]
        have hc : c ∈ Metric.ball c (8*δ) := Metric.mem_ball_self (by positivity)
        have hb := diskbound h c δ B hδ hB hhd (by
          intro w hw
          rw [Complex.sub_re, hre w hw, hre c hc]
          exact hlog w hw) z hz
        have hzmem : z ∈ Metric.ball c (8*δ) := by rw [Metric.mem_ball]; linarith
        rw [(hder z hzmem).deriv] at hb
        exact hb
      intro D hKhale q _ χ Q V δ v K T L σ c f hqQ hδ hd1 hv hvV hbudget hK hT hL hTL hup hlo hσlo hσhi
      have hz := diskzero hKhale q χ Q V δ v hqQ hδ hd1 hv hvV hbudget
      have hf : DifferentiableOn ℂ f (Metric.ball c (8*δ)) := by
        intro w hw
        exact (hz w (Metric.ball_subset_closedBall hw)).1.differentiableWithinAt
      have hn : ∀ w ∈ Metric.ball c (8*δ), f w ≠ 0 := by
        intro w hw
        exact (hz w (Metric.ball_subset_closedBall hw)).2
      have hB : 0 < K*(2*T+δ*L) := by positivity
      have hdiff : ∀ w ∈ Metric.ball c (8*δ),
          Real.log ‖f w‖ - Real.log ‖f c‖ ≤ K*(2*T+δ*L) := by
        intro w hw
        have hu := hup w hw
        nlinarith
      have hdist : dist ((σ:ℂ)+v*Complex.I) c ≤ 2*δ := by
        rw [dist_eq_norm]
        have he : (σ:ℂ)+v*Complex.I-c = (σ-(1+δ):ℝ) := by dsimp [c]; push_cast; ring
        rw [he, Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      constructor
      · exact (hz ((σ:ℂ)+v*Complex.I) (by
          rw [Metric.mem_closedBall]
          linarith)).2
      · have hb := logbound f c δ (K*(2*T+δ*L)) hδ hB hf hn hdiff
          ((σ:ℂ)+v*Complex.I) hdist
        apply hb.trans
        apply (div_le_iff₀ hδ).mpr
        nlinarith [mul_le_mul_of_nonneg_left hTL hK.le]
    have contour :
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (N δ a H t K Mv Mh : ℝ) (g : ℝ → ℂ),
      let R := Complex.reProdIm (Set.Icc (-δ) a) (Set.Icc (-H) H)
      let S : ℂ → ℂ := fun z => 1 - (t:ℂ)*Complex.I + z
      let f := DirichletCharacter.LFunction χ
      let F : ℂ → ℂ := fun z => mellin g z * (N:ℂ)^z * (-deriv f (S z) / f (S z))
      1 ≤ N → 0 ≤ δ → 0 ≤ a → 0 ≤ H → H < |t| → 0 ≤ Mv → 0 ≤ Mh →
      Continuous g → (∀ u : ℝ, u < 1/2 ∨ 3 < u → g u = 0) →
      (∀ z ∈ R, f (S z) ≠ 0) →
      (∀ z ∈ R, ‖deriv f (S z) / f (S z)‖ ≤ K) →
      (∀ y ∈ Set.Icc (-H) H, ‖mellin g ((-δ:ℝ) + (y:ℂ)*Complex.I)‖ ≤ Mv) →
      (∀ u ∈ Set.Icc (-δ) a, ‖mellin g ((u:ℂ)-H*Complex.I)‖ ≤ Mh ∧
        ‖mellin g ((u:ℂ)+H*Complex.I)‖ ≤ Mh) →
      ‖∫ y in (-H)..H, F ((a:ℂ)+y*Complex.I)‖ ≤
        2*H*(Mv*N^(-δ)*K) + 2*(a+δ)*(Mh*N^a*K) := by
      have rect :
        ∀ (F : ℂ → ℂ) (a b H Mv Mh : ℝ), a ≤ b → 0 ≤ H →
        DifferentiableOn ℂ F (Complex.reProdIm (Set.Icc a b) (Set.Icc (-H) H)) →
        (∀ y ∈ Set.Icc (-H) H, ‖F ((a:ℂ) + y*Complex.I)‖ ≤ Mv) →
        (∀ u ∈ Set.Icc a b, ‖F ((u:ℂ) - H*Complex.I)‖ ≤ Mh ∧
          ‖F ((u:ℂ) + H*Complex.I)‖ ≤ Mh) →
        ‖∫ y in (-H)..H, F ((b:ℂ) + y*Complex.I)‖ ≤ 2*H*Mv + 2*(b-a)*Mh := by
        intro F a b H Mv Mh hab hH hd hv hh
        have he := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
          ((a:ℂ) - H*Complex.I) ((b:ℂ) + H*Complex.I) (by
            simpa [Set.uIcc_of_le hab, Set.uIcc_of_le (show -H ≤ H by linarith)] using hd)
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.sub_im,
          Complex.mul_im, mul_one, zero_add, zero_sub, Complex.add_re, add_zero,
          Complex.add_im, Complex.real_smul, smul_eq_mul, Complex.ofReal_neg, neg_mul,
          ← sub_eq_add_neg] at he
        have hid :
          (∫ y in (-H)..H, F ((b:ℂ) + y*Complex.I)) =
          (∫ y in (-H)..H, F ((a:ℂ) + y*Complex.I)) +
          Complex.I * ((∫ u in a..b, F ((u:ℂ) - H*Complex.I)) -
            (∫ u in a..b, F ((u:ℂ) + H*Complex.I))) := by
          have alg (bot top right left : ℂ)
              (hh : bot-top+Complex.I*right-Complex.I*left=0) :
              right = left+Complex.I*(bot-top) := by
            linear_combination (norm := (ring_nf; simp [Complex.I_sq])) -Complex.I * hh
          exact alg _ _ _ _ he
        have hvl : ‖∫ y in (-H)..H, F ((a:ℂ)+y*Complex.I)‖ ≤ Mv*|H - -H| := intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => hv y (by
          have hh' : y ∈ Set.Ioc (-H) H := by simpa only [Set.uIoc_of_le (show -H ≤ H by linarith)] using hy
          exact ⟨hh'.1.le, hh'.2⟩))
        have hlo : ‖∫ u in a..b, F ((u:ℂ)-H*Complex.I)‖ ≤ Mh*|b-a| := intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => (hh u (by
          have hh' : u ∈ Set.Ioc a b := by simpa only [Set.uIoc_of_le hab] using hu
          exact ⟨hh'.1.le, hh'.2⟩)).1)
        have hhi : ‖∫ u in a..b, F ((u:ℂ)+H*Complex.I)‖ ≤ Mh*|b-a| := intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => (hh u (by
          have hh' : u ∈ Set.Ioc a b := by simpa only [Set.uIoc_of_le hab] using hu
          exact ⟨hh'.1.le, hh'.2⟩)).2)
        rw [abs_of_nonneg (by linarith : 0 ≤ H - -H)] at hvl
        rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hlo hhi
        rw [hid]
        calc
          _ ≤ ‖∫ y in (-H)..H, F ((a:ℂ)+y*Complex.I)‖ +
            ‖Complex.I * ((∫ u in a..b, F ((u:ℂ)-H*Complex.I)) -
              (∫ u in a..b, F ((u:ℂ)+H*Complex.I)))‖ := norm_add_le _ _
          _ ≤ Mv*(H - -H) + (Mh*(b-a) + Mh*(b-a)) := by
            rw [norm_mul, Complex.norm_I, one_mul]
            exact add_le_add hvl ((norm_sub_le _ _).trans (add_le_add hlo hhi))
          _ = _ := by ring
      have holo :
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (N a b H t : ℝ)
          (G : ℂ → ℂ),
        let R := Complex.reProdIm (Set.Icc a b) (Set.Icc (-H) H)
        let S : ℂ → ℂ := fun z => 1 - (t:ℂ)*Complex.I + z
        let F : ℂ → ℂ := fun z => G z * (N:ℂ)^z *
          (-(deriv (DirichletCharacter.LFunction χ) (S z)) / DirichletCharacter.LFunction χ (S z))
        0 < N → H < |t| → DifferentiableOn ℂ G R →
        (∀ z ∈ R, DirichletCharacter.LFunction χ (S z) ≠ 0) →
        DifferentiableOn ℂ F R := by
        intro q _ χ N a b H t G R S F hN ht hG hn
        have hmap : Set.MapsTo S R ({1}ᶜ : Set ℂ) := by
          intro z hz
          change S z ≠ 1
          intro he
          have hi := congrArg Complex.im he
          simp [S] at hi
          have hz' : z.re ∈ Set.Icc a b ∧ z.im ∈ Set.Icc (-H) H := hz
          have habs : |t| ≤ H := abs_le.mpr ⟨by linarith [hz'.2.1], by linarith [hz'.2.2]⟩
          exact (not_le_of_gt ht) habs
        have hL : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
          intro z hz
          exact (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
        have hD := hL.deriv isOpen_compl_singleton
        have hS : DifferentiableOn ℂ S R := by dsimp [S]; fun_prop
        have hP : DifferentiableOn ℂ (fun z : ℂ => (N:ℂ)^z) R := by
          have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
          fun_prop (disch := aesop)
        exact (hG.mul hP).mul (((hD.comp hS hmap).neg).div (hL.comp hS hmap) hn)
      have mellinhol :
        ∀ g : ℝ → ℂ, Continuous g →
        (∀ u : ℝ, u < 1/2 ∨ 3 < u → g u = 0) →
        Differentiable ℂ (mellin g) := by
        intro g hg hs z
        have htop (a : ℝ) : Asymptotics.IsBigO Filter.atTop g (fun u : ℝ => u ^ (-a)) := by
          apply Asymptotics.isBigO_iff.mpr
          refine ⟨1, ?_⟩
          filter_upwards [Filter.eventually_gt_atTop (3:ℝ)] with u hu
          simp [hs u (Or.inr hu)]
        have hbot (b : ℝ) : Asymptotics.IsBigO (nhdsWithin (0:ℝ) (Set.Ioi 0)) g
            (fun u : ℝ => u ^ (-b)) := by
          apply Asymptotics.isBigO_iff.mpr
          refine ⟨1, ?_⟩
          have he : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0), u < 1/2 :=
            (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2)).filter_mono nhdsWithin_le_nhds
          filter_upwards [he] with u hu
          simp [hs u (Or.inl hu)]
        exact (mellin_hasDerivAt_of_isBigO_rpow
          (hg.locallyIntegrable.locallyIntegrableOn (Set.Ioi 0)) (htop (z.re+1)) (by linarith)
          (hbot (z.re-1)) (by linarith)).2.differentiableAt
      intro q _ χ N δ a H t K Mv Mh g R S f F hN hδ ha hH ht hMv hMh hg hsupport hn hK hv hh
      have hNp : 0 < N := by linarith
      have hab : -δ ≤ a := by linarith
      have hG := (mellinhol g hg hsupport).differentiableOn (s := R)
      have hF := holo q χ N (-δ) a H t (mellin g) hNp ht hG hn
      have hnorm (z : ℂ) : ‖F z‖ =
          ‖mellin g z‖ * N^z.re * ‖deriv f (S z) / f (S z)‖ := by
        simp only [F, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hNp, neg_div, norm_neg]
      have hv' : ∀ y ∈ Set.Icc (-H) H, ‖F ((-δ:ℝ)+(y:ℂ)*Complex.I)‖ ≤ Mv*N^(-δ)*K := by
        intro y hy
        have hm : ((-δ:ℝ)+(y:ℂ)*Complex.I) ∈ R := by
          change _ ∈ Set.Icc (-δ) a ∧ _ ∈ Set.Icc (-H) H
          simpa using (show (-δ) ∈ Set.Icc (-δ) a ∧ y ∈ Set.Icc (-H) H from ⟨⟨le_rfl, hab⟩, hy⟩)
        rw [hnorm]
        have hpow : (((-δ:ℝ)+(y:ℂ)*Complex.I):ℂ).re = -δ := by simp
        rw [hpow]
        exact mul_le_mul (mul_le_mul_of_nonneg_right (hv y hy) (Real.rpow_nonneg hNp.le _))
          (hK _ hm) (norm_nonneg _) (mul_nonneg hMv (Real.rpow_nonneg hNp.le _))
      have hh' : ∀ u ∈ Set.Icc (-δ) a, ‖F ((u:ℂ)-H*Complex.I)‖ ≤ Mh*N^a*K ∧
          ‖F ((u:ℂ)+H*Complex.I)‖ ≤ Mh*N^a*K := by
        intro u hu
        have bound (z : ℂ) (hz : z ∈ R) (hzr : z.re = u) (hzG : ‖mellin g z‖ ≤ Mh) :
            ‖F z‖ ≤ Mh*N^a*K := by
          rw [hnorm, hzr]
          have hp := Real.rpow_le_rpow_of_exponent_le hN hu.2
          exact mul_le_mul (mul_le_mul hzG hp (Real.rpow_nonneg hNp.le _) hMh)
            (hK z hz) (norm_nonneg _) (mul_nonneg hMh (Real.rpow_nonneg hNp.le _))
        constructor
        · apply bound ((u:ℂ)-H*Complex.I) ?_ (by simp) (hh u hu).1
          change _ ∈ Set.Icc (-δ) a ∧ _ ∈ Set.Icc (-H) H
          simpa using (show u ∈ Set.Icc (-δ) a ∧ (-H) ∈ Set.Icc (-H) H from ⟨hu, le_rfl, by linarith⟩)
        · apply bound ((u:ℂ)+H*Complex.I) ?_ (by simp) (hh u hu).2
          change _ ∈ Set.Icc (-δ) a ∧ _ ∈ Set.Icc (-H) H
          simpa using (show u ∈ Set.Icc (-δ) a ∧ H ∈ Set.Icc (-H) H from ⟨hu, by linarith, le_rfl⟩)
      simpa only [sub_neg_eq_add] using rect F (-δ) a H (Mv*N^(-δ)*K) (Mh*N^a*K)
        hab hH hF hv' hh'
    intro D hKhale q _ χ N Q V δ a H t K T L Mv Mh g c f F
      hN hq hδ hd1 ha had hH ht htV hbudget hK hT hL hTL hMv hMh hg hs hup hlo hv hh
    have ht' : H < |t| := by linarith
    have geom (y : ℝ) (hy : y ∈ Set.Icc (-H) H) :
        20 ≤ |y-t| ∧ |y-t|+8*δ ≤ V := by
      have hyabs : |y| ≤ H := abs_le.mpr hy
      have htriangle : |t| ≤ |y-t|+|y| := by
        calc
          |t| = |(t-y)+y| := by congr 1; ring
          _ ≤ |t-y|+|y| := abs_add_le _ _
          _ = |y-t|+|y| := by rw [abs_sub_comm t y]
      have hu : |y-t| ≤ |t|+H := by
        apply abs_le.mpr
        constructor
        · linarith only [hy.1, le_abs_self t]
        · linarith only [hy.2, neg_abs_le t]
      constructor <;> linarith
    let R := Complex.reProdIm (Set.Icc (-δ) a) (Set.Icc (-H) H)
    let S : ℂ → ℂ := fun z => 1-(t:ℂ)*Complex.I+z
    have hrewrite (z : ℂ) : S z =
        ((1+z.re:ℝ):ℂ) + ((z.im-t:ℝ):ℂ)*Complex.I := by
      apply Complex.ext <;> simp [S] <;> ring
    have hzprops (z : ℂ) (hz : z ∈ R) :
        f (S z) ≠ 0 ∧ ‖deriv f (S z) / f (S z)‖ ≤ 3*K*L := by
      have hxy : z.re ∈ Set.Icc (-δ) a ∧ z.im ∈ Set.Icc (-H) H := hz
      obtain ⟨hlow,hhigh⟩ := geom z.im hxy.2
      have hσlo : 1-δ ≤ 1+z.re := by linarith [hxy.1.1]
      have hσhi : 1+z.re ≤ 1+δ := by linarith [hxy.1.2]
      have hb := strip hKhale q χ Q V δ (z.im-t) K T L (1+z.re)
        hq hδ hd1 hlow hhigh hbudget hK hT hL hTL
        (hup z.im hxy.2) (hlo z.im hxy.2) hσlo hσhi
      simpa only [hrewrite] using hb
    exact contour q χ N δ a H t (3*K*L) Mv Mh g hN hδ.le ha hH ht' hMv hMh hg hs
      (fun z hz => (hzprops z hz).1) (fun z hz => (hzprops z hz).2) hv hh
  obtain ⟨δ₀,hδ₀,hcenter⟩ := center
  refine ⟨δ₀,hδ₀,?_⟩
  intro D hKhale q _ χ N Q V δ a H t K T L Mv Mh g c f F
    hN hq hδ hsmall hd1 ha had hH ht htV hbudget hK hT hL hTL hMv hMh hg hs hup hnum hv hh
  exact reduction hKhale q χ N Q V δ a H t K T L Mv Mh g
    hN hq hδ hd1 ha had hH ht htV hbudget hK hT hL hTL hMv hMh hg hs hup
    (fun y _ => hnum.trans (hcenter δ hδ hsmall q χ (y-t)).2) hv hh

end Green64Analytic.LongPrime

end

/-! ## M1MellinEntire -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem compact_mellin_entire :
∀ g : ℝ → ℂ, Continuous g →
(∀ u : ℝ, u < 1/2 ∨ 3 < u → g u = 0) →
Differentiable ℂ (mellin g)
:= by
  intro g hg hs z
  have htop (a : ℝ) : Asymptotics.IsBigO Filter.atTop g (fun u : ℝ => u ^ (-a)) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨1, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop (3:ℝ)] with u hu
    simp [hs u (Or.inr hu)]
  have hbot (b : ℝ) : Asymptotics.IsBigO (nhdsWithin (0:ℝ) (Set.Ioi 0)) g
      (fun u : ℝ => u ^ (-b)) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨1, ?_⟩
    have he : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0), u < 1/2 :=
      (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [he] with u hu
    simp [hs u (Or.inl hu)]
  exact (mellin_hasDerivAt_of_isBigO_rpow
    (hg.locallyIntegrable.locallyIntegrableOn (Set.Ioi 0)) (htop (z.re+1)) (by linarith)
    (hbot (z.re-1)) (by linarith)).2.differentiableAt
end Green64Analytic.LongPrime

end

/-! ## PrimeAbel -/

section

open scoped BigOperators
open intervalIntegral MeasureTheory
namespace Green64Analytic.ReciprocalPrimeGrid

/-- Partial summation of a weighted integer counting measure at real endpoints. -/
theorem discrete_reciprocal_abel (c : ℕ → ℝ) (U V : ℝ)
    (hU : 1 < U) (hUV : U ≤ V) :
    ∑ k ∈ Finset.Ioc ⌊U⌋₊ ⌊V⌋₊, (k : ℝ)⁻¹ * c k =
    V⁻¹ * (∑ k ∈ Finset.Icc 0 ⌊V⌋₊, c k) -
    U⁻¹ * (∑ k ∈ Finset.Icc 0 ⌊U⌋₊, c k) +
    ∫ t in U..V, (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) / t ^ 2 := by
  have hU0 : 0 < U := lt_trans zero_lt_one hU
  have hdiff (t : ℝ) (ht : t ∈ Set.Icc U V) :
      DifferentiableAt ℝ (fun x : ℝ => x⁻¹) t := by
    exact (hasDerivAt_inv (ne_of_gt (hU0.trans_le ht.1))).differentiableAt
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc U V) :
      deriv (fun x : ℝ => x⁻¹) t = -(t ^ 2)⁻¹ := by
    exact (hasDerivAt_inv (ne_of_gt (hU0.trans_le ht.1))).deriv
  have hcont : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹)
      (Set.Icc U V) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht
      have htpos : 0 < t := hU0.trans_le ht.1
      exact pow_ne_zero _ (ne_of_gt htpos)
  have hint : IntegrableOn (deriv (fun x : ℝ => x⁻¹)) (Set.Icc U V) := by
    apply IntegrableOn.congr_fun (hcont.integrableOn_compact isCompact_Icc)
    · intro t ht
      exact (hderiv t ht).symm
    · exact measurableSet_Icc
  have hab := sum_mul_eq_sub_sub_integral_mul c hU0.le hUV hdiff hint
  have hintegral :
      (∫ t in Set.Ioc U V, deriv (fun x : ℝ => x⁻¹) t *
          (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)) =
      - ∫ t in U..V, (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) / t ^ 2 := by
    have heq :
      (∫ t in Set.Ioc U V, deriv (fun x : ℝ => x⁻¹) t *
          (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)) =
       ∫ t in Set.Ioc U V, -((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) / t ^ 2) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change deriv (fun x : ℝ => x⁻¹) t * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
        -((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) / t ^ 2)
      rw [hderiv t ⟨ht.1.le, ht.2⟩]
      simp [div_eq_mul_inv]
      ring
    rw [heq, MeasureTheory.integral_neg]
    rw [← intervalIntegral.integral_of_le hUV]
  rw [hintegral] at hab
  convert hab using 1 <;> ring

/-- Characteristic function of the *actual* natural primes. -/
def primeIndicator (n : ℕ) : ℝ := if n.Prime then 1 else 0

/-- Literal finite prime-counting mass up to the real argument. -/
noncomputable def primeCountReal (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeIndicator k

theorem primeCountReal_eq (t : ℝ) :
    primeCountReal t = (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
  unfold primeCountReal primeIndicator
  rw [← Nat.primesLE_card_eq_primeCounting]
  simp [Nat.primesLE_eq_filter_Icc_zero]

/-- Exact Abel summation of reciprocal natural primes, with no PNT hypothesis. -/
theorem prime_reciprocal_abel (U V : ℝ) (hU : 1 < U) (hUV : U ≤ V) :
    (∑ k ∈ Finset.Ioc ⌊U⌋₊ ⌊V⌋₊,
         if k.Prime then (k : ℝ)⁻¹ else 0) =
    primeCountReal V / V - primeCountReal U / U +
    ∫ t in U..V, primeCountReal t / t ^ 2 := by
  have h := discrete_reciprocal_abel primeIndicator U V hU hUV
  simpa [primeCountReal, primeIndicator, div_eq_mul_inv, mul_ite, mul_comm] using h

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## PrimeProductError -/

section

open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- Rectangular product-mass stability, using no measure-convergence black box. -/
theorem product_discrepancy {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℝ) (K ε : ℝ)
    (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (ha0 : ∀ i ∈ s, 0 ≤ a i)
    (ha : ∀ i ∈ s, a i ≤ K)
    (hb0 : ∀ i ∈ s, 0 ≤ b i)
    (hb : ∀ i ∈ s, b i ≤ K)
    (hgap : ∀ i ∈ s, |a i - b i| ≤ ε) :
    |(∏ i ∈ s, a i) - (∏ i ∈ s, b i)| ≤
       (s.card : ℝ) * ε * K ^ (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hsargs (j : ι) (hj : j ∈ s) : j ∈ insert i s :=
      Finset.mem_insert_of_mem hj
    have ia0 : 0 ≤ a i := ha0 i (Finset.mem_insert_self i s)
    have ia : a i ≤ K := ha i (Finset.mem_insert_self i s)
    have ib0 : 0 ≤ b i := hb0 i (Finset.mem_insert_self i s)
    have ib : b i ≤ K := hb i (Finset.mem_insert_self i s)
    have iegap : |a i - b i| ≤ ε := hgap i (Finset.mem_insert_self i s)
    have hh := ih
      (by intro j hj; exact ha0 j (hsargs j hj))
      (by intro j hj; exact ha j (hsargs j hj))
      (by intro j hj; exact hb0 j (hsargs j hj))
      (by intro j hj; exact hb j (hsargs j hj))
      (by intro j hj; exact hgap j (hsargs j hj))
    have hpa : 0 ≤ ∏ j ∈ s, a j :=
      Finset.prod_nonneg (by intro j hj; exact ha0 j (hsargs j hj))
    have hpaK : (∏ j ∈ s, a j) ≤ K ^ s.card := by
      calc
        _ ≤ ∏ _j ∈ s, K := by
          apply Finset.prod_le_prod₀
          · intro j hj; exact ha0 j (hsargs j hj)
          · intro j hj; exact ha j (hsargs j hj)
        _ = K ^ s.card := by simp
    have hsplit :
        a i * (∏ j ∈ s, a j) - b i * (∏ j ∈ s, b j) =
        (a i - b i) * (∏ j ∈ s, a j) +
        b i * ((∏ j ∈ s, a j) - (∏ j ∈ s, b j)) := by ring
    have hstep :
      |a i * (∏ j ∈ s, a j) - b i * (∏ j ∈ s, b j)| ≤
        ε * K ^ s.card + K * ((s.card : ℝ) * ε * K ^ (s.card - 1)) := by
      rw [hsplit]
      calc
        |(a i - b i) * (∏ j ∈ s, a j) +
            b i * ((∏ j ∈ s, a j) - (∏ j ∈ s, b j))| ≤
            |(a i - b i) * (∏ j ∈ s, a j)| +
            |b i * ((∏ j ∈ s, a j) - (∏ j ∈ s, b j))| := abs_add_le _ _
        _ = |a i - b i| * |∏ j ∈ s, a j| +
            |b i| * |(∏ j ∈ s, a j) - (∏ j ∈ s, b j)| := by
              simp only [abs_mul]
        _ ≤ ε * K ^ s.card + K * ((s.card : ℝ) * ε * K ^ (s.card - 1)) := by
              apply add_le_add
              · apply mul_le_mul iegap
                  (by simpa [abs_of_nonneg hpa] using hpaK)
                  (abs_nonneg _) hε
              · apply mul_le_mul
                  (by simpa [abs_of_nonneg ib0] using ib)
                  hh (abs_nonneg _) hK
    have hR :
      ε * K ^ s.card + K * ((s.card : ℝ) * ε * K ^ (s.card - 1)) =
        ((s.card + 1 : ℕ) : ℝ) * ε * K ^ s.card := by
      cases hc : s.card with
      | zero => simp
      | succ n =>
        simp only [Nat.add_sub_cancel_right, pow_succ]
        push_cast
        ring
    simpa [Finset.prod_insert hi, hi]
      using hstep.trans_eq hR

/-- Finite disjoint cell errors accumulate at most linearly in the number of cells. -/
theorem grid_union_discrepancy {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → ℝ) (δ : ℝ)
    (hcell : ∀ c ∈ s, |f c - g c| ≤ δ) :
    |(∑ c ∈ s, f c) - (∑ c ∈ s, g c)| ≤ (s.card : ℝ) * δ := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ c ∈ s, (f c - g c)| ≤ ∑ c ∈ s, |f c - g c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ s, δ := Finset.sum_le_sum (fun c hc => hcell c hc)
    _ = (s.card : ℝ) * δ := by simp

/-- Any fixed family of grid cells: full product mass and arbitrary unions. -/
theorem compact_grid_discrepancy (d k : ℕ)
    (μ ν : Fin d → Fin k → ℝ) (K ε : ℝ)
    (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hμ0 : ∀ i j, 0 ≤ μ i j) (hμ : ∀ i j, μ i j ≤ K)
    (hν0 : ∀ i j, 0 ≤ ν i j) (hν : ∀ i j, ν i j ≤ K)
    (hgap : ∀ i j, |μ i j - ν i j| ≤ ε)
    (S : Finset (Fin d → Fin k)) :
    |(∑ c ∈ S, ∏ i : Fin d, μ i (c i)) -
      (∑ c ∈ S, ∏ i : Fin d, ν i (c i))| ≤
      (S.card : ℝ) * ((d : ℝ) * ε * K ^ (d - 1)) := by
  apply grid_union_discrepancy
  intro c hc
  simpa using product_discrepancy
    (Finset.univ : Finset (Fin d))
    (fun i => μ i (c i)) (fun i => ν i (c i)) K ε hK hε
    (by simp [hμ0]) (by simp [hμ])
    (by simp [hν0]) (by simp [hν])
    (by simp [hgap])

/-- Explicit uniform estimate for any union of a fixed grid's cells. -/
theorem fixed_grid_from_interval_errors (d k : ℕ)
    (μ ν : Fin d → Fin k → ℝ) (H ε : ℝ)
    (hH : 0 ≤ H) (hε : 0 ≤ ε)
    (hμ0 : ∀ i j, 0 ≤ μ i j)
    (hν0 : ∀ i j, 0 ≤ ν i j) (hν : ∀ i j, ν i j ≤ H)
    (hgap : ∀ i j, |μ i j - ν i j| ≤ ε)
    (S : Finset (Fin d → Fin k)) :
    |(∑ c ∈ S, ∏ i : Fin d, μ i (c i)) -
      (∑ c ∈ S, ∏ i : Fin d, ν i (c i))| ≤
      (k : ℝ) ^ d * ((d : ℝ) * ε * (H + ε) ^ (d - 1)) := by
  have hμ (i : Fin d) (j : Fin k) : μ i j ≤ H + ε := by
    have := (abs_le.mp (hgap i j)).2
    linarith [hν i j]
  have hν' (i : Fin d) (j : Fin k) : ν i j ≤ H + ε := by
    linarith [hν i j]
  have hgrid := compact_grid_discrepancy d k μ ν (H + ε) ε
    (add_nonneg hH hε) hε hμ0 hμ hν0 hν' hgap S
  have hcard : (S.card : ℝ) ≤ (k : ℝ) ^ d := by
    have hn : S.card ≤ (Finset.univ : Finset (Fin d → Fin k)).card :=
      Finset.card_le_card (Finset.subset_univ S)
    simpa [Fintype.card_fun] using (Nat.cast_le.mpr hn :
      (S.card : ℝ) ≤ ((Finset.univ : Finset (Fin d → Fin k)).card : ℝ))
  exact hgrid.trans (mul_le_mul_of_nonneg_right hcard
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hε)
      (pow_nonneg (add_nonneg hH hε) _)))

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## PrimeTupleFibers -/

section

set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Green64Analytic.OrderedPrimeRough

/-- The exact first half of the rough-number lower comparison:
every finite fiber of ordered prime lists with the SAME product is
at most ell!, including multisets with repeated primes. -/
theorem prime_factor_fiber_le_factorial
    (F : Finset (List ℕ)) (ell n : ℕ)
    (hlen : ∀ l ∈ F, l.length = ell)
    (hprod : ∀ l ∈ F, l.prod = n)
    (hprimes : ∀ l ∈ F, ∀ p ∈ l, Nat.Prime p) :
    F.card ≤ ell.factorial := by
  classical
  by_cases hF : F = ∅
  · simp [hF]
  · have hn : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hF
    obtain ⟨l, hl⟩ := hn
    have hperm : l.Perm n.primeFactorsList :=
      Nat.primeFactorsList_unique (hprod l hl) (hprimes l hl)
    have hlen' : n.primeFactorsList.length = ell :=
      hperm.length_eq.symm.trans (hlen l hl)
    have hsub : F ⊆ n.primeFactorsList.permutations.toFinset := by
      intro t ht
      simp only [List.mem_toFinset, List.mem_permutations]
      exact Nat.primeFactorsList_unique (hprod t ht) (hprimes t ht)
    calc
      F.card ≤ n.primeFactorsList.permutations.toFinset.card :=
        Finset.card_le_card hsub
      _ ≤ n.primeFactorsList.permutations.length :=
        List.toFinset_card_le _
      _ = ell.factorial := by rw [List.length_permutations, hlen']

/-- The global factorial bound, valid for arbitrary finite subsets
of ordered prime lists, not just lists with distinct entries.

This is the exact counting-injection mechanism required by the
rough-number lower comparison; a fiber over any n has ≤ ell!
members, and the fibers partition the full ordered sample. -/
theorem ordered_prime_lists_card_le_factorial_mul
    (S : Finset (List ℕ)) (T : Finset ℕ) (ell : ℕ)
    (hlen : ∀ l ∈ S, l.length = ell)
    (hprimes : ∀ l ∈ S, ∀ p ∈ l, Nat.Prime p)
    (hmap : ∀ l ∈ S, l.prod ∈ T) :
    S.card ≤ ell.factorial * T.card := by
  classical
  have hm : Set.MapsTo (fun l : List ℕ => l.prod) (↑S : Set (List ℕ)) (↑T : Set ℕ) := by
    intro l hl
    exact hmap l (Finset.mem_coe.mp hl)
  have hsum := Finset.card_eq_sum_card_fiberwise (f := fun l : List ℕ => l.prod)
      (s := S) (t := T) hm
  calc
    S.card = ∑ n ∈ T, (S.filter fun l => l.prod = n).card := hsum
    _ ≤ ∑ _n ∈ T, ell.factorial := by
      apply Finset.sum_le_sum
      intro n hn
      apply prime_factor_fiber_le_factorial _ ell n
      · intro l hl
        exact hlen l (Finset.mem_filter.mp hl).1
      · intro l hl
        exact (Finset.mem_filter.mp hl).2
      · intro l hl p hp
        exact hprimes l (Finset.mem_filter.mp hl).1 p hp
    _ = ell.factorial * T.card := by simp [Nat.mul_comm]

end Green64Analytic.OrderedPrimeRough

end

/-! ## PrimeTupleRough -/

section

set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Green64Analytic.OrderedPrimeRough

/-- No squarefree hypothesis: every prime divisor of an ordered prime
product appears in the list, even when factors repeat. -/
theorem prime_dvd_list_prod_mem
    (l : List ℕ) (p : ℕ)
    (hpr : ∀ q ∈ l, Nat.Prime q) (hp : Nat.Prime p)
    (hdiv : p ∣ l.prod) : p ∈ l := by
  have hne : l.prod ≠ 0 := List.prod_ne_zero (by
    intro hz
    exact (hpr 0 hz).ne_zero rfl)
  have hc : p ∈ (l.prod).primeFactorsList :=
    (Nat.mem_primeFactorsList_iff_dvd hne hp).2 hdiv
  have hperm : l.Perm (l.prod).primeFactorsList :=
    Nat.primeFactorsList_unique rfl hpr
  exact hperm.mem_iff.mpr hc

theorem prime_list_product_rough
    (l : List ℕ) (z : ℝ)
    (hpr : ∀ q ∈ l, Nat.Prime q)
    (hbig : ∀ q ∈ l, z < (q:ℝ)) :
    ∀ p : ℕ, Nat.Prime p → (p:ℝ) ≤ z → ¬p ∣ l.prod := by
  intro p hp hpz hdiv
  have hmem := prime_dvd_list_prod_mem l p hpr hp hdiv
  exact not_lt_of_ge hpz (hbig p hmem)

/-- Ordinary non-squarefree rough integers; n=1 is retained. -/
noncomputable def roughSet (z x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ioc 0 (Nat.floor x)).filter
    (fun n => ∀ p : ℕ, Nat.Prime p → (p:ℝ) ≤ z → ¬ p ∣ n)


/-- Complete finite lower comparison, valid for ANY finite selection of
ordered prime tuples from a bounded product region. Repetitions among
the primes are allowed; ell=0 counts the empty list and n=1. -/
theorem prime_tuple_card_le_rough_card
    (S : Finset (List ℕ)) (ell : ℕ) (z x : ℝ)
    (hlen : ∀ l ∈ S, l.length = ell)
    (hprimes : ∀ l ∈ S, ∀ p ∈ l, Nat.Prime p)
    (hbig : ∀ l ∈ S, ∀ p ∈ l, z < (p:ℝ))
    (hprod : ∀ l ∈ S, (l.prod : ℝ) ≤ x) :
    S.card ≤ ell.factorial * (roughSet z x).card := by
  classical
  apply ordered_prime_lists_card_le_factorial_mul S (roughSet z x) ell
    hlen hprimes
  intro l hl
  have hpos : 0 < l.prod :=
    List.prod_pos (fun p hp => (hprimes l hl p hp).pos)
  have hfloor : l.prod ≤ Nat.floor x :=
    Nat.le_floor (hprod l hl)
  have hrough : ∀ p : ℕ, Nat.Prime p → (p:ℝ) ≤ z → ¬ p ∣ l.prod :=
    prime_list_product_rough l z (hprimes l hl) (hbig l hl)
  simp only [roughSet, Finset.mem_filter, Finset.mem_Ioc]
  exact ⟨⟨hpos,hfloor⟩,hrough⟩

end Green64Analytic.OrderedPrimeRough

end

/-! ## S2MellinInterval -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem mellin_interval :
∀ (a b : ℝ) (g : ℝ → ℂ) (s : ℂ),
  0 < a → a ≤ b →
  (∀ t : ℝ, t ≤ a ∨ b < t → g t = 0) →
  mellin g s = ∫ t in a..b, (t:ℂ)^(s-1) * g t :=
by
  intro a b g s ha hab hsupport
  have hsub : Set.Ioc a b ⊆ Set.Ioi (0:ℝ) := by
    intro t ht
    exact ha.trans ht.1
  have hzero : ∀ t ∈ (Set.Ioi (0:ℝ)) \ (Set.Ioc a b),
    (t:ℂ)^(s-1) * g t = 0 := by
    intro t ht
    have hout : t ≤ a ∨ b < t := by
      by_contra hn
      push_neg at hn
      exact ht.2 ⟨hn.1,hn.2⟩
    simp [hsupport t hout]
  unfold mellin
  simp only [smul_eq_mul]
  calc
    (∫ t : ℝ in Set.Ioi 0, (t:ℂ)^(s-1) * g t) =
      (∫ t : ℝ in Set.Ioc a b, (t:ℂ)^(s-1) * g t) :=
        MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        measurableSet_Ioi hsub hzero
    _ = ∫ t in a..b, (t:ℂ)^(s-1) * g t := by
      rw [intervalIntegral.integral_of_le hab]
end Green64Analytic.LongPrime

end

/-! ## SourceActualFrequencyCutoffBudget -/

section

namespace Green64Analytic.CorrelationMellin

/-! A single source cutoff L^B0+|sigma1| works for both the
literal high U1 estimate and the all-gcd low discrepancy estimate.
The required log budgets follow from the source's bounded shifts,
not from new high/low energy hypotheses. -/
theorem source_actual_one_cutoff_shift_budget
    (L B0 sigma0 sigma1 : ℝ) (s0 s1 : ℕ)
    (hL : 3 ≤ L) (hB : B0 ≤ (s1:ℝ))
    (hSigma0 : |sigma0| ≤ L^s0)
    (hSigma1 : |sigma1| ≤ L^s1) :
    0 ≤ L^B0+|sigma1|+2 ∧
    L^B0+|sigma1|+2 ≤ L^(s1+2) ∧
    L^B0+|sigma1|+2+|sigma0| ≤ L^(s0+s1+3) := by
  have hLone : 1 ≤ L := by linarith
  have hLpos : 0 ≤ L := by linarith
  have hBpow : L^B0 ≤ L^s1 := by
    have hb := Real.rpow_le_rpow_of_exponent_le hLone hB
    simpa only [Real.rpow_natCast] using hb
  have hPow1 : (1:ℝ) ≤ L^s1 := by
    simpa using (pow_le_pow_right₀ hLone (Nat.zero_le s1) :
      L^0 ≤ L^s1)
  have hLsq : (4:ℝ) ≤ L^2 := by
    nlinarith [sq_nonneg (L-3)]
  have hCut : L^B0+|sigma1|+2 ≤ L^(s1+2) := by
    calc
      _ ≤ 4*L^s1 := by linarith
      _ ≤ L^2*L^s1 :=
        mul_le_mul_of_nonneg_right hLsq (pow_nonneg hLpos _)
      _ = L^(s1+2) := by rw [pow_add]; ring
  let e : ℕ := s0+s1+2
  have he0 : s0 ≤ e := by dsimp [e]; omega
  have he1 : s1+2 ≤ e := by dsimp [e]; omega
  have hPow0 : L^s0 ≤ L^e :=
    pow_le_pow_right₀ hLone he0
  have hPow1' : L^(s1+2) ≤ L^e :=
    pow_le_pow_right₀ hLone he1
  have hLtwo : (2:ℝ) ≤ L := by linarith
  have hFreq : L^B0+|sigma1|+2+|sigma0| ≤ L^(s0+s1+3) := by
    calc
      _ ≤ 2*L^e := by linarith
      _ ≤ L*L^e :=
        mul_le_mul_of_nonneg_right hLtwo (pow_nonneg hLpos _)
      _ = L^(e+1) := by rw [pow_succ]; ring
      _ = L^(s0+s1+3) := by
        congr 1
  exact ⟨by positivity, hCut, hFreq⟩
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualJointRationalCharacter -/

section

namespace Green64Analytic.CorrelationMellin

/-! Original source gcd/character expansion produces the product of
the initial character chi0 and a character modulo the reduced
rational modulus.  On source rough alpha-support these are units
modulo their product, so the product is an actual Dirichlet character
at the product modulus.  No separate discrepancy hypothesis is used. -/

noncomputable def sourceJointCharacter
    (qBase q : ℕ) (chi0 : DirichletCharacter ℂ qBase)
    (xi : DirichletCharacter ℂ q) :
    DirichletCharacter ℂ (qBase*q) :=
  (DirichletCharacter.changeLevel (Nat.dvd_mul_right qBase q) chi0) *
    (DirichletCharacter.changeLevel (Nat.dvd_mul_left q qBase) xi)

theorem source_joint_character_source_unit_exact
    (qBase q : ℕ) (chi0 : DirichletCharacter ℂ qBase)
    (xi : DirichletCharacter ℂ q) (m : ℤ)
    (hm : IsCoprime m (qBase*q)) :
    sourceJointCharacter qBase q chi0 xi
       (m : ZMod (qBase*q)) =
      chi0 (m : ZMod qBase) * xi (m : ZMod q) := by
  have hBase :=
    DirichletCharacter.changeLevel_eq_cast_of_dvd'
      chi0 (Nat.dvd_mul_right qBase q) hm
  have hRat :=
    DirichletCharacter.changeLevel_eq_cast_of_dvd'
      xi (Nat.dvd_mul_left q qBase) hm
  unfold sourceJointCharacter
  rw [MulChar.mul_apply]
  rw [hBase, hRat]
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualPrimeMinEventually -/

section

open Filter
namespace Green64Analytic.CorrelationMellin

/-! The original small prime cutoff exp(L^a), a>0, exceeds
all fixed comparison constants, eventually. Consequently
one source comparison bound on H' implies the stronger U1
Mellin window inequality, without another source assumption. -/
theorem eventually_source_short_prime_comparison_lower
    (a Ccomp : ℝ) (ha : 0 < a) (hC : 0 < Ccomp) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (P : ℕ) (N : ℝ), 1 ≤ N →
      Real.exp (L^a) ≤ ((2*P:ℕ):ℝ) →
      Ccomp ≤ (P:ℝ)*(⌈N⌉₊:ℝ) ∧
      2 ≤ Ccomp*(P:ℝ) := by
  have hExp :
      Tendsto (fun L : ℝ => Real.exp (L^a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop ha)
  filter_upwards [hExp.eventually (eventually_ge_atTop
    (max (2*Ccomp) (4/Ccomp)))] with L hLarge
  intro P N hN hP
  have hPpos : (0:ℝ) ≤ P := Nat.cast_nonneg P
  have hPmin : Ccomp ≤ (P:ℝ) := by
    have hh : (2*Ccomp) ≤ Real.exp (L^a) := (le_max_left _ _).trans hLarge
    have hp : Real.exp (L^a) ≤ 2*(P:ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hP
    linarith
  have hProd : 2 ≤ Ccomp*(P:ℝ) := by
    have hh : 4/Ccomp ≤ Real.exp (L^a) :=
      (le_max_right _ _).trans hLarge
    have hp : Real.exp (L^a) ≤ 2*(P:ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hP
    have hc := (div_le_iff₀ hC).mp (hh.trans hp)
    nlinarith
  have hNceil : (1:ℝ) ≤ (⌈N⌉₊:ℝ) := by
    exact hN.trans (Nat.le_ceil N)
  constructor
  · nlinarith [mul_nonneg hPpos (sub_nonneg.mpr hNceil)]
  · exact hProd

/-- A single original free-product lower bound implies high U1's
stronger T+2 support inequality once the small prime is large. -/
theorem source_actual_strong_free_scale_of_small_prime
    (L Ccomp P Hprime Carc : ℝ)
    (hL : 0 ≤ L) (hC : 2 ≤ Ccomp*P)
    (hFree : 2*L*Ccomp*P*L^Carc ≤ Hprime) :
    4*L*L^Carc ≤ Hprime := by
  have hRpow : 0 ≤ L^Carc := Real.rpow_nonneg hL _
  have hMultiplier : 0 ≤ 2*L*L^Carc := by positivity
  have hh := mul_le_mul_of_nonneg_left hC hMultiplier
  nlinarith [hh, hFree]
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualPrimeScaleEventually -/

section

open Filter
namespace Green64Analytic.CorrelationMellin

/-! The source b<1, eta<1/4 and genuine Y=x^(1+o(1))
scale imply the 3/5 U1 product splitting. The natural source
prime dyad ceil N is kept exactly, without replacing it by N. -/
theorem eventually_source_prime_scale_below_two_fifths
    (b η Ccomp : ℝ)
    (hb : b < 1) (hη : η < 1/4) (hC : 0 < Ccomp) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (P : ℕ) (N Y : ℝ),
      1 ≤ N → Real.exp (3*L/4) ≤ Y →
      (P:ℝ) ≤ Real.exp (L^b) →
      N ≤ Real.exp (η*L) →
      2*Ccomp*(P:ℝ)*(⌈N⌉₊:ℝ) ≤ (⌈Y⌉₊:ℝ)^(2/5:ℝ) := by
  let eps : ℝ := ((3/10:ℝ)-η)/2
  have heps : 0 < eps := by
    dsimp [eps]
    linarith
  have hPowLimit :=
    tendsto_rpow_neg_atTop (by linarith : 0 < (1:ℝ)-b)
  have hSmallEventually : ∀ᶠ L : ℝ in atTop, L^b ≤ eps*L := by
    filter_upwards [hPowLimit.eventually (eventually_lt_nhds heps),
      eventually_gt_atTop (0:ℝ)] with L hSmall hLp
    have hEq : L^(-((1:ℝ)-b)) = L^b/L := by
      rw [show -((1:ℝ)-b)=b-1 by ring, Real.rpow_sub hLp,
        Real.rpow_one]
    rw [hEq] at hSmall
    exact (div_le_iff₀ hLp).mp (le_of_lt hSmall)
  have hExpLimit :
      Tendsto (fun L : ℝ => Real.exp (eps*L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      ((tendsto_const_mul_atTop_of_pos heps).2 tendsto_id)
  filter_upwards [hSmallEventually,
      hExpLimit.eventually (eventually_ge_atTop (4*Ccomp))]
    with L hLpow hCexp
  intro P N Y hN hY hP hNmax
  have hNp : (0:ℝ) ≤ N := by linarith
  have hNceil : (⌈N⌉₊:ℝ) ≤ 2*Real.exp (η*L) := by
    have hc := Nat.ceil_lt_add_one hNp
    linarith
  have hPpow : Real.exp (L^b) ≤ Real.exp (eps*L) :=
    Real.exp_le_exp.mpr hLpow
  have hProd :
      4*Ccomp*Real.exp (L^b)*Real.exp (η*L) ≤
      Real.exp ((3/10:ℝ)*L) := by
    calc
      _ ≤ Real.exp (eps*L)*Real.exp (L^b)*Real.exp (η*L) := by
        gcongr
      _ ≤ Real.exp (eps*L)*Real.exp (eps*L)*Real.exp (η*L) := by
        gcongr
      _ = Real.exp ((3/10:ℝ)*L) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [eps]
        ring
  have hYceil : Real.exp (3*L/4) ≤ (⌈Y⌉₊:ℝ) :=
    hY.trans (Nat.le_ceil Y)
  have hYpow :=
    Real.rpow_le_rpow (Real.exp_pos _).le hYceil
      (by norm_num : (0:ℝ) ≤ (2/5:ℝ))
  have hPowerIdentity :
      (Real.exp (3*L/4))^(2/5:ℝ) =
      Real.exp ((3/10:ℝ)*L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  calc
    2*Ccomp*(P:ℝ)*(⌈N⌉₊:ℝ) ≤
        2*Ccomp*Real.exp (L^b)*(2*Real.exp (η*L)) := by
      gcongr
    _ = 4*Ccomp*Real.exp (L^b)*Real.exp (η*L) := by ring
    _ ≤ Real.exp ((3/10:ℝ)*L) := hProd
    _ ≤ (⌈Y⌉₊:ℝ)^(2/5:ℝ) := by
      simpa only [hPowerIdentity] using hYpow
end Green64Analytic.CorrelationMellin

end

/-! ## SourceContinuousFourierL1MeanSquare -/

section

open MeasureTheory

namespace Green64Analytic.CorrelationMellin

/-!
Continuous-frequency Minkowski bridge in Banach-valued form.

For the intended application, E is the L² space on the Mellin interval,
G ξ is the shifted literal source four-factor polynomial, and K is the
actual Fourier kernel (or its tail).  Thus the hypothesis ‖G ξ‖² ≤ B is
exactly the uniform all-shift mean-square estimate, while the conclusion
costs only the square of the Fourier L¹ mass.

This theorem does not by itself construct the L²-valued map or prove its
Bochner integral agrees a.e. with the scalar Fourier integral.  That
Fubini/L²-lift is the remaining formal bridge.
-/
theorem source_continuous_fourier_l1_mean_square
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : ℝ → ℂ) (G : ℝ → E) (S : Set ℝ) (B mass : ℝ)
    (hB : 0 ≤ B) (hmass : 0 ≤ mass)
    (hK : IntegrableOn (fun ξ => ‖K ξ‖) S)
    (hKG : IntegrableOn (fun ξ => K ξ • G ξ) S)
    (hGB : ∀ᵐ ξ ∂volume.restrict S, ‖G ξ‖^2 ≤ B)
    (hKmass : (∫ ξ in S, ‖K ξ‖) ≤ mass) :
    ‖∫ ξ in S, K ξ • G ξ‖^2 ≤ mass^2 * B := by
  have hNorm : IntegrableOn (fun ξ => ‖K ξ‖ * ‖G ξ‖) S := by
    change Integrable (fun ξ => ‖K ξ‖ * ‖G ξ‖) (volume.restrict S)
    simpa only [norm_smul] using hKG.norm
  have hRight : IntegrableOn (fun ξ => Real.sqrt B * ‖K ξ‖) S :=
    hK.const_mul (Real.sqrt B)
  have hPoint : ∀ᵐ ξ ∂volume.restrict S,
      ‖K ξ‖ * ‖G ξ‖ ≤ Real.sqrt B * ‖K ξ‖ := by
    filter_upwards [hGB] with ξ hξ
    have hsqrt : ‖G ξ‖ ≤ Real.sqrt B := by
      have hs0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
      have hs2 : (Real.sqrt B)^2 = B := Real.sq_sqrt hB
      nlinarith [norm_nonneg (G ξ)]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hsqrt (norm_nonneg (K ξ))
  have hIntBound :
      (∫ ξ in S, ‖K ξ‖ * ‖G ξ‖) ≤
        ∫ ξ in S, Real.sqrt B * ‖K ξ‖ :=
    integral_mono_ae hNorm hRight hPoint
  have hNormInt :
      ‖∫ ξ in S, K ξ • G ξ‖ ≤ ∫ ξ in S, ‖K ξ‖ * ‖G ξ‖ := by
    simpa only [norm_smul] using
      (norm_integral_le_integral_norm
        (μ := volume.restrict S) (fun ξ => K ξ • G ξ))
  have hToMass :
      (∫ ξ in S, Real.sqrt B * ‖K ξ‖) ≤ Real.sqrt B * mass := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hKmass (Real.sqrt_nonneg B)
  have hMain : ‖∫ ξ in S, K ξ • G ξ‖ ≤ Real.sqrt B * mass :=
    hNormInt.trans (hIntBound.trans hToMass)
  have hsqrt0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hsqrt2 : (Real.sqrt B)^2 = B := Real.sq_sqrt hB
  nlinarith [norm_nonneg (∫ ξ in S, K ξ • G ξ)]

end Green64Analytic.CorrelationMellin

end

/-! ## SourceDirichletApproximation -/

section

namespace Green64Analytic.CorrelationD

/-- Dirichlet approximation in the literal C6 variables, with
the reduced integral numerator and positive natural denominator.
The second inequality is the exact |beta| <= r^(-2)
required by the source C6 kernel. -/
theorem source_exists_reduced_dirichlet_approximation
    (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (a : ℤ) (r : ℕ),
      0 < r ∧ r ≤ Q ∧ Int.gcd a (r:ℤ) = 1 ∧
      |ξ - (a:ℝ)/(r:ℝ)| ≤
        1/(((Q:ℝ)+1)*(r:ℝ)) ∧
      |ξ - (a:ℝ)/(r:ℝ)| ≤ 1/((r:ℝ)^2) := by
  obtain ⟨q,hq,hden⟩ :=
    Real.exists_rat_abs_sub_le_and_den_le ξ hQ
  have hr : 0 < q.den := Rat.den_pos q
  have hcop : Int.gcd q.num (q.den:ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs]
    simpa only [Int.natAbs_natCast] using q.reduced
  have hc : (q:ℝ) = (q.num:ℝ)/(q.den:ℝ) := Rat.cast_def q
  have hbound : |ξ - (q.num:ℝ)/(q.den:ℝ)| ≤
      1/(((Q:ℝ)+1)*(q.den:ℝ)) := by
    simpa only [hc] using hq
  have hrR : (0:ℝ) < (q.den:ℝ) := by exact_mod_cast hr
  have hN : (q.den:ℝ) ≤ (Q:ℝ)+1 := by
    have hcast : (q.den:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hden
    linarith
  have hden2 : (q.den:ℝ)^2 ≤ ((Q:ℝ)+1)*(q.den:ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) hrR.le]
  have hrt : |ξ - (q.num:ℝ)/(q.den:ℝ)| ≤
      1/((q.den:ℝ)^2) := by
    exact hbound.trans (one_div_le_one_div_of_le (pow_pos hrR 2) hden2)
  exact ⟨q.num,q.den,hr,hden,hcop,hbound,hrt⟩
end Green64Analytic.CorrelationD

end

/-! ## SourceDirichletExact -/

section

namespace Green64Analytic.CorrelationD

/-- Actual reduced Dirichlet approximation, satisfying *both* the
finite Q approximation and C6's original |beta|≤ r^-2 restriction.
No irrationality hypothesis, including rational frequencies. -/
theorem source_dirichlet_reduced_c6 (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (a : ℤ) (r : ℕ),
      0 < r ∧ r ≤ Q ∧ Int.gcd a (r : ℤ) = 1 ∧
      |ξ - (a : ℝ)/(r:ℝ)| ≤ 1/(((Q:ℝ)+1)*(r:ℝ)) ∧
      |ξ - (a : ℝ)/(r:ℝ)| ≤ 1/((r:ℝ)^2) := by
  obtain ⟨q, happrox, hden⟩ :=
    Real.exists_rat_abs_sub_le_and_den_le ξ hQ
  let a : ℤ := q.num
  let r : ℕ := q.den
  have hrpos : 0 < r := q.den_pos
  have hcop : Int.gcd a (r : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs]
    simpa only [a, r, Int.natAbs_natCast] using q.reduced
  have hcast : (q:ℝ) = (a:ℝ)/(r:ℝ) := by
    simpa only [a, r] using (Rat.cast_def (K := ℝ) q)
  have happrox' :
      |ξ - (a:ℝ)/(r:ℝ)| ≤ 1/(((Q:ℝ)+1)*(r:ℝ)) := by
    rw [← hcast]
    exact happrox
  have hrle : (r:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hden
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hrpos
  have hdencomp : (r:ℝ)^2 ≤ ((Q:ℝ)+1)*(r:ℝ) := by
    nlinarith
  have hC6 :
      |ξ - (a:ℝ)/(r:ℝ)| ≤ 1/((r:ℝ)^2) :=
    happrox'.trans (one_div_le_one_div_of_le (by positivity) hdencomp)
  exact ⟨a,r,hrpos,hden,hcop,happrox',hC6⟩
end Green64Analytic.CorrelationD

end

/-! ## SourceDirichletFloorCap -/

section

namespace Green64Analytic.CorrelationD

/-- Literal source denominator choice Q=⌊H'/R⌋, including the exact
Dirichlet rational approximation to kθ. No free or generic Q is
assumed. The same reduced a/r is immediately admissible for C6. -/
theorem source_dirichlet_floor_Hprime
    (k : ℤ) (theta Hprime R : ℝ)
    (hR : 0 < R) (hH : R ≤ Hprime) :
    let Q : ℕ := ⌊Hprime/R⌋₊
    0 < Q ∧
    ∃ (a : ℤ) (r : ℕ),
      0 < r ∧ r ≤ Q ∧ (r:ℝ) ≤ Hprime/R ∧
      Int.gcd a (r : ℤ) = 1 ∧
      |(k:ℝ)*theta-(a:ℝ)/(r:ℝ)| ≤
        1/(((Q:ℝ)+1)*(r:ℝ)) ∧
      |(k:ℝ)*theta-(a:ℝ)/(r:ℝ)| ≤
        1/((r:ℝ)^2) := by
  dsimp only
  let Q : ℕ := ⌊Hprime/R⌋₊
  have hHR : (1:ℝ) ≤ Hprime/R :=
    (le_div_iff₀ hR).mpr (by simpa using hH)
  have hQ : 0 < Q := by
    have h1 : 1 ≤ Q := Nat.le_floor (n := 1) (by simpa using hHR)
    omega
  obtain ⟨a,r,hr,hcap,hgcd,hDir,hC6⟩ :=
    source_dirichlet_reduced_c6 ((k:ℝ)*theta) Q hQ
  have hcast : (r:ℝ) ≤ Hprime/R :=
    (by exact_mod_cast hcap : (r:ℝ) ≤ (Q:ℝ)).trans
      (Nat.floor_le (by positivity : 0 ≤ Hprime/R))
  exact ⟨hQ,a,r,hr,hcap,hcast,hgcd,hDir,hC6⟩
end Green64Analytic.CorrelationD

end

