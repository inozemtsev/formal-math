module

public import Green64.Library.Sieve.Foundation.Lemma9.Part005
public import Green64.Library.Analysis.Estimates.Part002
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic
public import Green64.Library.Weights.Part021
public import Green64.Library.Correlation.Part001
public import Green64.Library.Correlation.Part002
public import Mathlib
public import Green64.Library.Weights.Part012
public import Green64.Library.Sieve.Foundations.Part002
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Green64.Library.Correlation.Part003
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# Weights / Part023

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceLogPhaseBridge -/

section

/-! Bridge from the imported discrete additive character to the exact
source Mellin character exp(i t log n). No surrogate phase. -/
namespace Green64Analytic.CorrelationMellin

theorem sourceSaltLogF_phase (delta : ℝ) (n : ℕ) :
    Salt.ExpSum.eK (sourceSaltLogF delta n) = sourcePhase n (-delta) := by
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  have hreal : 2 * Real.pi *
      (-(delta / (2 * Real.pi)) * Real.log (n:ℝ)) =
      (-delta) * Real.log (n:ℝ) := by
    field_simp [hpi]
  unfold Salt.ExpSum.eK sourceSaltLogF sourcePhase
  rw [hreal]
  congr 1
  ring

theorem sourcePhase_complete_flip (delta : ℝ) (U : ℕ) :
    ‖∑ n ∈ Finset.Icc U (4*U), sourcePhase n delta‖ =
    ‖∑ n ∈ Finset.Icc U (4*U), sourcePhase n (-delta)‖ := by
  have hConj : (∑ n ∈ Finset.Icc U (4*U), sourcePhase n (-delta)) =
      (starRingEnd ℂ) (∑ n ∈ Finset.Icc U (4*U), sourcePhase n delta) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    exact sourcePhase_neg n delta
  rw [hConj]
  exact (RCLike.norm_conj _).symm

theorem sourcePhase_complete_to_Salt (delta : ℝ) (U : ℕ) :
    ‖∑ n ∈ Finset.Icc U (4*U), sourcePhase n (-delta)‖ =
    ‖∑ n ∈ Finset.Icc U (4*U),
        Salt.ExpSum.eK (sourceSaltLogF delta n)‖ := by
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro n hn
  exact (sourceSaltLogF_phase delta n).symm
end Green64Analytic.CorrelationMellin

end

/-! ## SourceOriginalLogSumBounds -/

section

/-! Actual source Mellin phase, signed real frequency, and both
unconditional derivative sum tests on the complete [U,4U] block. -/
namespace Green64Analytic.CorrelationMellin

theorem sourcePhase_complete_first_pos (delta : ℝ) (U : ℕ)
    (hd : 0 < delta) (hU : 1 ≤ U) (hdU : delta ≤ (U:ℝ)) :
    ‖∑ n ∈ Finset.Icc U (4*U), sourcePhase n delta‖ ≤
      40*(U:ℝ)/delta := by
  calc
    _ = ‖∑ n ∈ Finset.Icc U (4*U), sourcePhase n (-delta)‖ :=
      sourcePhase_complete_flip delta U
    _ = ‖∑ n ∈ Finset.Icc U (4*U),
        Salt.ExpSum.eK (sourceSaltLogF delta n)‖ :=
      sourcePhase_complete_to_Salt delta U
    _ ≤ _ := sourceSaltLog_complete_first delta U hd hU hdU

theorem sourcePhase_complete_second_pos (delta : ℝ) (U : ℕ)
    (hd : 0 < delta) (hU : 1 ≤ U) :
    ‖∑ n ∈ Finset.Icc U (4*U), sourcePhase n delta‖ ≤
      128*Real.sqrt delta + 192*(U:ℝ)/Real.sqrt delta := by
  calc
    _ = ‖∑ n ∈ Finset.Icc U (4*U), sourcePhase n (-delta)‖ :=
      sourcePhase_complete_flip delta U
    _ = ‖∑ n ∈ Finset.Icc U (4*U),
        Salt.ExpSum.eK (sourceSaltLogF delta n)‖ :=
      sourcePhase_complete_to_Salt delta U
    _ ≤ _ := sourceSaltLog_complete_second delta U hd hU

theorem sourcePhase_complete_first_signed (delta : ℝ) (U : ℕ)
    (hU : 1 ≤ U) (hd : 0 < |delta|) (hdU : |delta| ≤ (U:ℝ)) :
    ‖∑ n ∈ Finset.Icc U (4*U), sourcePhase n delta‖ ≤
      40*(U:ℝ)/|delta| := by
  rcases le_total 0 delta with hpos | hneg
  · rw [abs_of_nonneg hpos] at hd hdU ⊢
    exact sourcePhase_complete_first_pos delta U hd hU hdU
  · have heq : |delta| = -delta := abs_of_nonpos hneg
    rw [heq] at hd hdU ⊢
    rw [sourcePhase_complete_flip delta U]
    exact sourcePhase_complete_first_pos (-delta) U hd hU hdU

theorem sourcePhase_complete_second_signed (delta : ℝ) (U : ℕ)
    (hU : 1 ≤ U) (hd : 0 < |delta|) :
    ‖∑ n ∈ Finset.Icc U (4*U), sourcePhase n delta‖ ≤
      128*Real.sqrt |delta| + 192*(U:ℝ)/Real.sqrt |delta| := by
  rcases le_total 0 delta with hpos | hneg
  · rw [abs_of_nonneg hpos] at hd ⊢
    exact sourcePhase_complete_second_pos delta U hd hU
  · have heq : |delta| = -delta := abs_of_nonpos hneg
    rw [heq] at hd ⊢
    rw [sourcePhase_complete_flip delta U]
    exact sourcePhase_complete_second_pos (-delta) U hd hU
end Green64Analytic.CorrelationMellin

end

/-! ## SourceScaleAsymptotics -/

section

open Filter Real
set_option maxHeartbeats 8000000
namespace Green64Analytic.CorrelationD

/-- A fixed logarithmic-power modulus is eventually below
    every genuine stretched-exponential source prime cutoff. -/
theorem eventually_rpow_lt_exp_rpow (a C : ℝ) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, L^C < Real.exp (L^a) := by
  have hlimit : Tendsto (fun L : ℝ =>
      Real.exp (L^a) / (L^a)^(C/a)) atTop atTop :=
    (tendsto_exp_div_rpow_atTop (C/a)).comp (tendsto_rpow_atTop ha)
  have hratio : ∀ᶠ L : ℝ in atTop,
      (1:ℝ) < Real.exp (L^a) / (L^a)^(C/a) :=
    hlimit.eventually (eventually_gt_atTop (1:ℝ))
  filter_upwards [hratio, eventually_ge_atTop (1:ℝ)] with L hrat hL
  have hp : 0 < L := by linarith
  have heq : (L^a)^(C/a) = L^C := by
    rw [← Real.rpow_mul (le_of_lt hp)]
    congr 1
    field_simp
  rw [heq] at hrat
  have hden : 0 < L^C := Real.rpow_pos_of_pos hp C
  simpa only [one_mul] using (lt_div_iff₀ hden).mp hrat

theorem eventually_rpow_lt_exp_linear (τ C : ℝ) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop, L^C < Real.exp (τ*L) := by
  have hlimit : Tendsto (fun L : ℝ => Real.exp (τ*L)/L^C)
      atTop atTop :=
    tendsto_exp_mul_div_rpow_atTop C τ hτ
  have hratio : ∀ᶠ L : ℝ in atTop,
      (1:ℝ) < Real.exp (τ*L)/L^C :=
    hlimit.eventually (eventually_gt_atTop (1:ℝ))
  filter_upwards [hratio, eventually_ge_atTop (1:ℝ)] with L hrat hL
  have hp : 0 < L := by linarith
  have hden : 0 < L^C := Real.rpow_pos_of_pos hp C
  simpa only [one_mul] using (lt_div_iff₀ hden).mp hrat

theorem eventually_source_scales (a τ C : ℝ)
    (ha : 0 < a) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop,
      L^C < Real.exp (Real.sqrt L) ∧
      L^C < Real.exp (L^a) ∧
      L^C < Real.exp (τ*L) := by
  have hW := eventually_rpow_lt_exp_rpow ((1:ℝ)/2) C (by norm_num)
  have hS := eventually_rpow_lt_exp_rpow a C ha
  have hP := eventually_rpow_lt_exp_linear τ C hτ
  filter_upwards [hW, hS, hP] with L hw hs hp
  exact ⟨by simpa only [Real.sqrt_eq_rpow] using hw, hs, hp⟩
end Green64Analytic.CorrelationD

end

/-! ## SourceArcExponentialBudget -/

section

open Filter Real
open scoped BigOperators

/-- Exact quantitative rational-center count at the source
polylogarithmic Q-scale. -/
theorem source_rational_center_polylog_budget
    (Q : ℕ) (L B : ℝ) (hL : 1 ≤ L) (hB : 0 ≤ B)
    (hQ : (Q:ℝ) ≤ L^B) :
    ((Q*(Q+1):ℕ):ℝ) ≤ 2*L^(2*B) := by
  have hLp : 0 < L := by linarith
  have hLB : 1 ≤ L^B := by
    have hh := Real.rpow_le_rpow_of_exponent_le hL hB
    simpa only [Real.rpow_zero] using hh
  have hQp : ((Q+1:ℕ):ℝ) ≤ 2*L^B := by
    push_cast
    linarith
  have hprod :
      (Q:ℝ) * ((Q+1:ℕ):ℝ) ≤ L^B*(2*L^B) :=
    mul_le_mul hQ hQp (by positivity) (by positivity)
  calc
    ((Q*(Q+1):ℕ):ℝ) = (Q:ℝ)*((Q+1:ℕ):ℝ) := by push_cast; ring
    _ ≤ L^B*(2*L^B) := hprod
    _ = 2*L^(2*B) := by
      rw [show 2*B = B+B by ring, Real.rpow_add hLp]
      ring

/-- Every fixed power and positive scalar is eventually swallowed
by exp(L^a). This gives a fully quantified L^{-A} budget, without
assuming a generic exponential saving lemma at the output. -/
theorem eventually_source_fixed_poly_exp_saving
    (a K C A : ℝ) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧ K*L^C*Real.exp (-(L^a)) ≤ 1/L^A := by
  have hdom :=
    Green64Analytic.CorrelationD.eventually_rpow_lt_exp_rpow
      a (C+A+1) ha
  have hlarge := eventually_ge_atTop (max (2:ℝ) K)
  filter_upwards [hdom,hlarge] with L hdom hlarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hlarge |>.trans' (by norm_num)
  have hLp : 0 < L := by linarith
  have hK : K ≤ L := (le_max_right _ _).trans hlarge
  have hCpos : 0 ≤ L^C := (Real.rpow_pos_of_pos hLp C).le
  have hApos : 0 < L^A := Real.rpow_pos_of_pos hLp A
  have hKbound : K*L^C*L^A ≤ L*L^C*L^A := by
    have hh := mul_le_mul_of_nonneg_right hK hCpos
    exact mul_le_mul_of_nonneg_right hh hApos.le
  have hPowEq : L*L^C*L^A = L^(C+A+1) := by
    rw [show C+A+1 = (C+A)+1 by ring,
      Real.rpow_add hLp, Real.rpow_add hLp]
    simp only [Real.rpow_one]
    ring
  have hproduct : K*L^C*L^A ≤ Real.exp (L^a) := by
    calc
      _ ≤ L*L^C*L^A := hKbound
      _ = L^(C+A+1) := hPowEq
      _ ≤ Real.exp (L^a) := hdom.le
  have hExpPos : 0 < Real.exp (L^a) := Real.exp_pos _
  have hdivide : K*L^C / Real.exp (L^a) ≤ 1/L^A := by
    apply (div_le_div_iff₀ hExpPos hApos).mpr
    simpa only [one_mul] using hproduct
  refine ⟨hL, ?_⟩
  calc
    K*L^C*Real.exp (-(L^a)) =
        K*L^C / Real.exp (L^a) := by rw [Real.exp_neg]; ring
    _ ≤ 1/L^A := hdivide

end

/-! ## SourceActualArcRatioSaving -/

section

open Filter
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1500000

/-- Arbitrary log saving for the source linear/log ratio, uniformly in
all later x,Z,H',Y. The source identity Y=ZH' is used exactly. -/
theorem eventually_source_actual_arc_ratio_saving434
    (Carc CZ K E target : ℝ) (hCarc : 0 ≤ Carc) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ x Z Hprime Y : ℝ,
      0 < x → L = Real.log x → x*L^(-CZ) ≤ Z →
      0 < Hprime → Y = Z*Hprime →
      K*((Hprime/L^Carc)/Y)^2*L^E ≤ 1/L^target := by
  have hDecay := eventually_source_fixed_poly_exp_saving 1 K (E+2*CZ) target (by norm_num)
  filter_upwards [hDecay] with L hDecayL
  obtain ⟨hL,hDecayL⟩ := hDecayL
  intro x Z Hprime Y hx hLog hZ hH hY
  have hLp : 0 < L := by linarith
  have hBound := source_actual_arc_ratio_exp_bound434
    L x Z Hprime Y Carc CZ hL hx hLog hZ hH hY hCarc
  have hZp : 0 < Z := (mul_pos hx (Real.rpow_pos_of_pos hLp _)).trans_le hZ
  have hYp : 0 < Y := by rw [hY]; positivity
  have hRatio : 0 ≤ (Hprime/L^Carc)/Y := by positivity
  have hSquare : ((Hprime/L^Carc)/Y)^2 ≤ (L^CZ*Real.exp (-L))^2 := by nlinarith
  have hExp : Real.exp (-L)*Real.exp (-L) ≤ Real.exp (-L) := by
    rw [←Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hPower : L^E * (L^CZ)^2 = L^(E+2*CZ) := by
    rw [Real.rpow_add hLp,show 2*CZ = CZ*2 by ring,Real.rpow_mul hLp.le]
    norm_num
  calc
    _ ≤ K*(L^CZ*Real.exp (-L))^2*L^E := by gcongr
    _ = K*(L^E*(L^CZ)^2)*(Real.exp (-L)*Real.exp (-L)) := by ring
    _ ≤ K*(L^E*(L^CZ)^2)*Real.exp (-L) :=
      mul_le_mul_of_nonneg_left hExp (by positivity)
    _ = K*L^(E+2*CZ)*Real.exp (-(L^(1:ℝ))) := by rw [hPower,Real.rpow_one]
    _ ≤ _ := hDecayL
end Green64Analytic.CorrelationSquare

end

/-! ## SourceArcReplacementSaving -/

section

open Filter
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1800000

/-- Absorb the actual linear/log replacement with the source scale identity,
not an assumed approximation-energy estimate. -/
theorem eventually_source_arc_replacement_saving434
    (A Carc CZ R B0 E target : ℝ)
    (hA : 1 ≤ A) (hCarc : 0 ≤ Carc) (hR : 0 ≤ R) (hB0 : 0 ≤ B0) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ ∀ x Z Hprime Y B : ℝ,
      0 < x → L = Real.log x → x*L^(-CZ) ≤ Z →
      0 < Hprime → Y = Z*Hprime → 1 ≤ Y →
      Real.log Y ≤ (3/2:ℝ)*L → 0 ≤ B → B ≤ B0*L^E →
      R*((Hprime/L^Carc)/Y)^2*
        (B^2*(Nat.ceil (A*Y):ℝ)*(1+Real.log (Nat.ceil (A*Y):ℝ))^63) ≤
      Y/L^target := by
  let CQ : ℝ := 2*A*(Real.log (2*A)+5/2)^63
  have hLogA : 0 ≤ Real.log (2*A) := Real.log_nonneg (by linarith)
  have hCQ : 0 ≤ CQ := by dsimp [CQ]; positivity
  have hDecay := eventually_source_actual_arc_ratio_saving434 Carc CZ
    (R*(B0^2*CQ)) (2*E+63) target hCarc (by positivity)
  filter_upwards [hDecay,eventually_ge_atTop (1:ℝ)] with L hDecayL hL
  refine ⟨hL,?_⟩
  intro x Z Hprime Y B hx hLog hZ hH hY hYone hlogY hB hCap
  have hMoment := source_arc_moment_amplitude434 A Y L B B0 E 63
    hA hYone hL hlogY hB hB0 hCap le_rfl
  have hSave := hDecayL x Z Hprime Y hx hLog hZ hH hY
  calc
    _ ≤ R*((Hprime/L^Carc)/Y)^2*((B0^2*CQ)*Y*L^(2*E+63)) :=
      mul_le_mul_of_nonneg_left hMoment (by positivity)
    _ = Y*((R*(B0^2*CQ))*((Hprime/L^Carc)/Y)^2*L^(2*E+63)) := by ring
    _ ≤ Y*(1/L^target) := mul_le_mul_of_nonneg_left hSave (by linarith)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceArcSquareSaving -/

section

open Filter
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1800000

/-- The original square residual is negligible on the physical Y-window,
including growing-group and harmonic-mass polynomial losses. -/
theorem eventually_source_arc_square_saving434
    (A a B0 E V0 Vexp target : ℝ)
    (hA : 1 ≤ A) (ha : 0 < a) (hB0 : 0 ≤ B0) (hV0 : 0 ≤ V0) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ ∀ Y B V : ℝ,
      1 ≤ Y → Real.log Y ≤ (3/2:ℝ)*L →
      0 ≤ B → B ≤ B0*L^E → 0 ≤ V → V ≤ V0*L^Vexp →
      V*(B^2*(Nat.ceil (A*Y):ℝ)*(1+Real.log (Nat.ceil (A*Y):ℝ))^16)*
        Real.exp (-(L^a)) ≤ Y/L^target := by
  let CQ : ℝ := 2*A*(Real.log (2*A)+5/2)^63
  have hLogA : 0 ≤ Real.log (2*A) := Real.log_nonneg (by linarith)
  have hCQ : 0 ≤ CQ := by dsimp [CQ]; positivity
  have hDecay := eventually_source_fixed_poly_exp_saving a
    (V0*(B0^2*CQ)) (Vexp+(2*E+63)) target ha
  filter_upwards [hDecay] with L hDecayL
  obtain ⟨hL,hSave⟩ := hDecayL
  refine ⟨hL,?_⟩
  intro Y B V hY hlogY hB hCap hV hVCap
  have hLp : 0 < L := by linarith
  have hMoment := source_arc_moment_amplitude434 A Y L B B0 E 16
    hA hY hL hlogY hB hB0 hCap (by norm_num)
  calc
    _ ≤ V*((B0^2*CQ)*Y*L^(2*E+63))*Real.exp (-(L^a)) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMoment hV)
        (Real.exp_pos _).le
    _ ≤ (V0*L^Vexp)*((B0^2*CQ)*Y*L^(2*E+63))*Real.exp (-(L^a)) := by
      gcongr
    _ = Y*((V0*(B0^2*CQ))*L^(Vexp+(2*E+63))*Real.exp (-(L^a))) := by
      simp only [Real.rpow_add hLp]; ring
    _ ≤ Y*(1/L^target) := mul_le_mul_of_nonneg_left hSave (by linarith)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceEventuallyStretched -/

section

open Filter Real

namespace Green64Analytic.CorrelationD

/-- Source comparison cells have lower endpoints exp(L^c-O(1)).
This eventually dominates every fixed L-power, **including** the
constant loss in the exponential. -/
theorem eventually_source_comparison_lower
    (c W C : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, L^W < Real.exp (L^c-C) := by
  have hdom : ∀ᶠ L : ℝ in atTop,
      L^(W+1) < Real.exp (L^c) :=
    eventually_rpow_lt_exp_rpow c (W+1) hc
  have hsize : ∀ᶠ L : ℝ in atTop, Real.exp C ≤ L :=
    eventually_ge_atTop (Real.exp C)
  filter_upwards [hdom, hsize] with L hdom hsize
  have hLp : 0 < L := lt_of_lt_of_le (Real.exp_pos C) hsize
  have hpow : 0 ≤ L^W := (Real.rpow_pos_of_pos hLp W).le
  have hprod : L^W*Real.exp C ≤ L^W*L :=
    mul_le_mul_of_nonneg_left hsize hpow
  have hpowEq : L^W*L = L^(W+1) := by
    rw [Real.rpow_add hLp]
    simp
  have hlimit : L^W*Real.exp C < Real.exp (L^c) := by
    calc
      _ ≤ L^W*L := hprod
      _ = L^(W+1) := hpowEq
      _ < Real.exp (L^c) := hdom
  rw [Real.exp_sub]
  exact (lt_div_iff₀ (Real.exp_pos C)).mpr hlimit
end Green64Analytic.CorrelationD

end

/-! ## SourceEventuallyLogBudget -/

section

open Filter Real

namespace Green64Analytic.CorrelationD

/-- For d<A and d≥0, the original source logarithm
T=log L times L^d is eventually dominated by L^A.
The log(2) term matches the unreduced denominator log(2r). -/
theorem eventually_source_log_dominance
    (d A C : ℝ) (hd : 0 ≤ d) (hdA : d < A) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      Real.log 2 + C*Real.log L*L^d ≤ L^A := by
  let eps : ℝ := (A-d)/2
  have heps : 0 < eps := by dsimp [eps]; linarith
  have hApos : 0 < A := lt_of_le_of_lt hd hdA
  have hEpsBig : ∀ᶠ L : ℝ in atTop,
      2*C/eps ≤ L^eps :=
    (tendsto_rpow_atTop heps).eventually
      (eventually_ge_atTop (2*C/eps))
  have hABig : ∀ᶠ L : ℝ in atTop,
      2*Real.log 2 ≤ L^A :=
    (tendsto_rpow_atTop hApos).eventually
      (eventually_ge_atTop (2*Real.log 2))
  filter_upwards [hEpsBig, hABig, eventually_ge_atTop (1:ℝ)]
    with L hEpsBig hABig hL
  have hLp : 0 < L := by linarith
  have hlog : Real.log L ≤ L^eps/eps :=
    Real.log_le_rpow_div hLp.le heps
  have hdPow : 0 ≤ L^d := (Real.rpow_pos_of_pos hLp d).le
  have hPow : 0 ≤ L^(eps+d) := (Real.rpow_pos_of_pos hLp _).le
  have hBound : C/eps ≤ L^eps/2 := by
    calc
      C/eps = (2*C/eps)/2 := by ring
      _ ≤ L^eps/2 :=
        div_le_div_of_nonneg_right hEpsBig (by norm_num)
  have hTerm1 : C*Real.log L*L^d ≤
      C*(L^eps/eps)*L^d := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog hC) hdPow
  have hTermEq : C*(L^eps/eps)*L^d =
      (C/eps)*L^(eps+d) := by
    rw [Real.rpow_add hLp]
    field_simp
  have hTerm2 : (C/eps)*L^(eps+d) ≤
      (L^eps/2)*L^(eps+d) :=
    mul_le_mul_of_nonneg_right hBound hPow
  have hPowerId : (L^eps)*(L^(eps+d)) = L^A := by
    rw [← Real.rpow_add hLp]
    congr 1
    dsimp [eps]
    ring
  have hTerm3 : (L^eps/2)*L^(eps+d) = L^A/2 := by
    calc
      _ = (L^eps*L^(eps+d))/2 := by ring
      _ = L^A/2 := by rw [hPowerId]
  have hLogTerm : C*Real.log L*L^d ≤ L^A/2 :=
    hTerm1.trans (hTermEq.le.trans (hTerm2.trans hTerm3.le))
  linarith
end Green64Analytic.CorrelationD

end

/-! ## SourceLogDenominatorCap -/

section

open Filter Real

namespace Green64Analytic.CorrelationD

/-- The true H' upper scale gives the log(2r) control used in the
source C6 minor-arc proof, without assuming that bound separately. -/
theorem source_log_denominator_from_hprime
    (L d A C r Hprime : ℝ)
    (hr : 0 < r) (hH : 0 < Hprime)
    (hrH : r ≤ Hprime)
    (hHexp : Hprime ≤ Real.exp (C*Real.log L*L^d))
    (hdom : Real.log 2+C*Real.log L*L^d ≤ L^A) :
    Real.log (2*r) ≤ L^A := by
  have hExpPos : 0 < Real.exp (C*Real.log L*L^d) :=
    Real.exp_pos _
  have h2 : 2*r ≤ 2*Real.exp (C*Real.log L*L^d) := by
    calc
      2*r ≤ 2*Hprime := mul_le_mul_of_nonneg_left hrH (by norm_num)
      _ ≤ 2*Real.exp (C*Real.log L*L^d) :=
        mul_le_mul_of_nonneg_left hHexp (by norm_num)
  have hlog : Real.log (2*r) ≤
      Real.log (2*Real.exp (C*Real.log L*L^d)) :=
    Real.log_le_log (by positivity) h2
  have heq : Real.log (2*Real.exp (C*Real.log L*L^d)) =
      Real.log 2+C*Real.log L*L^d := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0)
      (Real.exp_ne_zero _), Real.log_exp]
  calc
    Real.log (2*r) ≤
      Real.log (2*Real.exp (C*Real.log L*L^d)) := hlog
    _ = Real.log 2+C*Real.log L*L^d := heq
    _ ≤ L^A := hdom

/-- Eventual log-budget uniform in **every** real denominator r
under the original source H' stretched upper scale. -/
theorem eventually_source_all_denominator_logs
    (d A C : ℝ) (hd : 0 ≤ d) (hdA : d < A) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      ∀ r Hprime : ℝ,
        0 < r →
        0 < Hprime →
        r ≤ Hprime →
        Hprime ≤ Real.exp (C*Real.log L*L^d) →
        Real.log (2*r) ≤ L^A := by
  filter_upwards [eventually_source_log_dominance d A C hd hdA hC]
    with L hdom r Hprime hr hHp hrH hHexp
  exact source_log_denominator_from_hprime
    L d A C r Hprime hr hHp hrH hHexp hdom
end Green64Analytic.CorrelationD

end

/-! ## SourceEventuallyMinorScale -/

section

open Filter Real

namespace Green64Analytic.CorrelationD

/-- The actual stretched-exponential lower source comparison scales
and the logarithmic upper H' scale jointly discharge all analytic
hypotheses in the four-term C6 bracket except the genuine rational
approximation denominator window. -/
theorem eventually_source_four_term_minor_budget
    (c d A B C₁ C₂ Chigh : ℝ)
    (hc : 0 < c) (hd : 0 ≤ d) (hdA : d < A)
    (hB : 0 ≤ B) (hChigh : 0 ≤ Chigh) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧
      ∀ (U₁ U₂ Hprime r : ℝ),
        Real.exp (L^c-C₁) ≤ U₁ →
        Real.exp (L^c-C₂) ≤ U₂ →
        Hprime = U₁*U₂ →
        0 < Hprime →
        0 < r →
        r ≤ Hprime →
        Hprime ≤ Real.exp (Chigh*Real.log L*L^d) →
        L^B ≤ r →
        r ≤ Hprime/L^(A+B) →
        1/U₂+1/r+Real.log (2*r)/U₁+
          r*Real.log (2*r)/(U₁*U₂) ≤ 4/L^B := by
  have hLower₁ := eventually_source_comparison_lower c (A+B) C₁ hc
  have hLower₂ := eventually_source_comparison_lower c B C₂ hc
  have hLog := eventually_source_all_denominator_logs d A Chigh hd hdA hChigh
  have hA : 0 ≤ A := le_trans hd (le_of_lt hdA)
  filter_upwards [hLower₁,hLower₂,hLog,eventually_ge_atTop (1:ℝ)]
    with L hlo₁ hlo₂ hlog hL
  refine ⟨hL, ?_⟩
  intro U₁ U₂ Hprime r hU₁ hU₂ hH hHp hr hrH hHhi hrlo hrhi
  have hScale₁ : L^(A+B) ≤ U₁ := hlo₁.le.trans hU₁
  have hScale₂ : L^B ≤ U₂ := hlo₂.le.trans hU₂
  have hLogBound : Real.log (2*r) ≤ L^A :=
    hlog r Hprime hr hHp hrH hHhi
  have hRpow : 1 ≤ L^B := by
    have htmp :=
      Real.rpow_le_rpow_of_exponent_le hL
        (show (0:ℝ) ≤ B from hB)
    simpa only [Real.rpow_zero] using htmp
  have hrOne : 1 ≤ r := hRpow.trans hrlo
  have hLog0 : 0 ≤ Real.log (2*r) :=
    Real.log_nonneg (by nlinarith)
  have hrhi' : r ≤ U₁*U₂/L^(A+B) := by
    rw [hH] at hrhi
    exact hrhi
  exact Green64SourceC6.source_large_denominator_four_term_save
    L A B U₁ U₂ r hL hA hB hScale₁ hScale₂
    hrlo hrhi' hLog0 hLogBound
end Green64Analytic.CorrelationD

end

/-! ## SourceDirichletDenominatorScale -/

section

open Filter Real

namespace Green64Analytic.CorrelationD

/-- Dirichlet's source cap r ≤ H'/L^Cprime implies both
r ≤ H' and the smaller upper cap needed by C6 whenever
Cprime ≥ A+B. The entire source four-term large-r saving
then follows eventually, with only the genuine r ≥ L^B
minor-arc condition and source original scales remaining. -/
theorem eventually_source_minor_from_dirichlet_cap
    (c d A B Cprime C₁ C₂ Chigh : ℝ)
    (hc : 0 < c) (hd : 0 ≤ d) (hdA : d < A)
    (hB : 0 ≤ B) (hCprime : A+B ≤ Cprime)
    (hChigh : 0 ≤ Chigh) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧
      ∀ (U₁ U₂ Hprime r : ℝ),
        Real.exp (L^c-C₁) ≤ U₁ →
        Real.exp (L^c-C₂) ≤ U₂ →
        Hprime = U₁*U₂ →
        0 < Hprime →
        0 < r →
        Hprime ≤ Real.exp (Chigh*Real.log L*L^d) →
        L^B ≤ r →
        r ≤ Hprime/L^Cprime →
        1/U₂+1/r+Real.log (2*r)/U₁+
          r*Real.log (2*r)/(U₁*U₂) ≤ 4/L^B := by
  have hevent := eventually_source_four_term_minor_budget
    c d A B C₁ C₂ Chigh hc hd hdA hB hChigh
  filter_upwards [hevent] with L hsource
  obtain ⟨hL, hbound⟩ := hsource
  refine ⟨hL, ?_⟩
  intro U₁ U₂ Hprime r hU₁ hU₂ hH hHp hr hHhi hrlo hrCap
  have hLp : 0 < L := by linarith
  have hAB : 0 ≤ A+B := by linarith
  have hCp : 0 ≤ Cprime := le_trans hAB hCprime
  have hpC : 0 < L^Cprime := Real.rpow_pos_of_pos hLp Cprime
  have hpAB : 0 < L^(A+B) := Real.rpow_pos_of_pos hLp (A+B)
  have hone : 1 ≤ L^Cprime := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hL hCp)
  have hHcap : Hprime/L^Cprime ≤ Hprime := by
    apply (div_le_iff₀ hpC).mpr
    calc
      Hprime ≤ Hprime*1 := by simp
      _ ≤ Hprime*L^Cprime := mul_le_mul_of_nonneg_left hone hHp.le
  have hrH : r ≤ Hprime := hrCap.trans hHcap
  have hExp : L^(A+B) ≤ L^Cprime :=
    Real.rpow_le_rpow_of_exponent_le hL hCprime
  have hQ : Hprime/L^Cprime ≤ Hprime/L^(A+B) :=
    div_le_div_of_nonneg_left hHp.le hpAB hExp
  have hrCap' : r ≤ Hprime/L^(A+B) := hrCap.trans hQ
  exact hbound U₁ U₂ Hprime r hU₁ hU₂ hH hHp hr hrH hHhi hrlo hrCap'
end Green64Analytic.CorrelationD

end

/-! ## SourceDenominatorNonempty -/

section

open Filter Real

namespace Green64Analytic.CorrelationD

/-- The actual source Dirichlet maximum denominator
Q=floor(H'/L^Cprime) is eventually positive, rather than being
postulated as an available large rational search range. -/
theorem eventually_source_dirichlet_range_nonempty
    (c C₁ C₂ Cprime : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (U₁ U₂ Hprime : ℝ),
        Real.exp (L^c-C₁) ≤ U₁ →
        Real.exp (L^c-C₂) ≤ U₂ →
        Hprime = U₁*U₂ →
        0 < Nat.floor (Hprime/L^Cprime) := by
  have h₁ := eventually_source_comparison_lower c Cprime C₁ hc
  have h₂ := eventually_source_comparison_lower c 0 C₂ hc
  filter_upwards [h₁,h₂,eventually_ge_atTop (1:ℝ)]
    with L hlow₁ hlow₂ hL U₁ U₂ Hprime hu₁ hu₂ hH
  have hLp : 0 < L := by linarith
  have hQp : 0 < L^Cprime := Real.rpow_pos_of_pos hLp Cprime
  have hS₁ : L^Cprime ≤ U₁ := hlow₁.le.trans hu₁
  have hS₂ : 1 ≤ U₂ := by
    have hbase : (1:ℝ) = L^((0:ℝ)) := by simp
    rw [hbase]
    exact hlow₂.le.trans hu₂
  have hHbig : L^Cprime ≤ Hprime := by
    rw [hH]
    calc
      L^Cprime = L^Cprime*1 := by ring
      _ ≤ U₁*U₂ :=
        mul_le_mul hS₁ hS₂ (by linarith) (le_trans hQp.le hS₁)
  have hRatio : (1:ℝ) ≤ Hprime/L^Cprime :=
    (le_div_iff₀ hQp).mpr (by simpa only [one_mul] using hHbig)
  exact Nat.floor_pos.mpr hRatio
end Green64Analytic.CorrelationD

end

/-! ## SourceEventualMajorMinorSplit -/

section

open Filter Real

namespace Green64Analytic.CorrelationD

/-- The source's full Dirichlet major/minor denominator split,
not merely a conditional large-r bound. The approximation denominator
is literally floor(H'/L^Cprime); the small/large threshold is
ceil(L^B). Thus every kθ satisfies one of the stated alternatives. -/
theorem eventually_source_major_minor_split
    (c d A B Cprime C₁ C₂ Chigh : ℝ)
    (hc : 0 < c) (hd : 0 ≤ d) (hdA : d < A)
    (hB : 0 ≤ B) (hCprime : A+B ≤ Cprime)
    (hChigh : 0 ≤ Chigh) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧
      ∀ (U₁ U₂ Hprime : ℝ),
        Real.exp (L^c-C₁) ≤ U₁ →
        Real.exp (L^c-C₂) ≤ U₂ →
        Hprime = U₁*U₂ →
        0 < Hprime →
        Hprime ≤ Real.exp (Chigh*Real.log L*L^d) →
        ∀ (theta : ℝ) (k : ℤ), k ≠ 0 →
        let Q := Nat.floor (Hprime/L^Cprime)
        let R := Nat.ceil (L^B)
        ∃ (a : ℤ) (r : ℕ),
          0 < r ∧ r ≤ Q ∧ Int.gcd a (r:ℤ) = 1 ∧
          |(k:ℝ)*theta-(a:ℝ)/(r:ℝ)| ≤
            1/(((Q:ℝ)+1)*(r:ℝ)) ∧
          |(k:ℝ)*theta-(a:ℝ)/(r:ℝ)| ≤ 1/((r:ℝ)^2) ∧
          ((L^B ≤ (r:ℝ) ∧
            1/U₂+1/(r:ℝ)+Real.log (2*(r:ℝ))/U₁+
              (r:ℝ)*Real.log (2*(r:ℝ))/(U₁*U₂) ≤ 4/L^B)
            ∨ ∃ (h : ℤ) (q : ℕ) (shift : ℤ),
              r < R ∧ q = k.natAbs*r ∧ 0 < q ∧
              q ≤ k.natAbs*Q ∧ 0 ≤ h ∧ h < (q:ℤ) ∧
              |theta-(shift:ℝ)-(h:ℝ)/(q:ℝ)| ≤
                (1/(((Q:ℝ)+1)*(r:ℝ)))/|(k:ℝ)|) := by
  have hQevt :=
    eventually_source_dirichlet_range_nonempty c C₁ C₂ Cprime hc
  have hMevt :=
    eventually_source_minor_from_dirichlet_cap
      c d A B Cprime C₁ C₂ Chigh hc hd hdA hB hCprime hChigh
  filter_upwards [hQevt,hMevt] with L hQ hMinor
  obtain ⟨hL,hMain⟩ := hMinor
  refine ⟨hL,?_⟩
  intro U₁ U₂ Hprime hU₁ hU₂ hH hHp hHhi theta k hk
  dsimp only
  let Q : ℕ := Nat.floor (Hprime/L^Cprime)
  let R : ℕ := Nat.ceil (L^B)
  have hQpos : 0 < Q := hQ U₁ U₂ Hprime hU₁ hU₂ hH
  obtain ⟨a,r,hr,hrQ,hcop,hnear,hbeta,hCase⟩ :=
    source_dirichlet_major_minor_dichotomy k theta Q R hk hQpos
  refine ⟨a,r,hr,hrQ,hcop,hnear,hbeta,?_⟩
  rcases hCase with hlarge | hsmall
  · left
    have hR : L^B ≤ (r:ℝ) := by
      have hceil : (L^B:ℝ) ≤ (R:ℝ) := Nat.le_ceil _
      have hnat : (R:ℝ) ≤ (r:ℝ) := by exact_mod_cast hlarge
      exact hceil.trans hnat
    have hLpos : 0 < L := by linarith
    have hDenpos : 0 < L^Cprime :=
      Real.rpow_pos_of_pos hLpos Cprime
    have hRatio : (Q:ℝ) ≤ Hprime/L^Cprime :=
      Nat.floor_le (div_nonneg hHp.le hDenpos.le)
    have hCap : (r:ℝ) ≤ Hprime/L^Cprime := by
      have hcast : (r:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hrQ
      exact hcast.trans hRatio
    have hrReal : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
    have hBound := hMain U₁ U₂ Hprime (r:ℝ)
      hU₁ hU₂ hH hHp hrReal hHhi hR hCap
    exact ⟨hR,hBound⟩
  · right
    exact hsmall
end Green64Analytic.CorrelationD

end

/-! ## SourceArcRadius -/

section

namespace Green64Analytic.CorrelationD

/-- The exact unreduced Dirichlet arc radius produced by lifting
kθ through Q=floor(H'/L^Cprime) is never larger than L^Cprime/H'.
It holds uniformly for all nonzero signed k and all positive r. -/
theorem source_floor_dirichlet_arc_radius
    (Hprime L Cprime : ℝ) (Q r : ℕ) (k : ℤ)
    (hHp : 0 < Hprime) (hL : 0 < L)
    (hQ : Q = Nat.floor (Hprime/L^Cprime))
    (hr : 0 < r) (hk : k ≠ 0) :
    (1/(((Q:ℝ)+1)*(r:ℝ)))/|(k:ℝ)| ≤
      L^Cprime/Hprime := by
  have hLpow : 0 < L^Cprime := Real.rpow_pos_of_pos hL Cprime
  have hQ0 : (0:ℝ) < (Q:ℝ)+1 := by positivity
  have hrR : (1:ℝ) ≤ (r:ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hr))
  have hkNat : 1 ≤ k.natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hk)
  have hkAbs : (1:ℝ) ≤ |(k:ℝ)| := by
    have hcast : (1:ℝ) ≤ (k.natAbs:ℝ) := by exact_mod_cast hkNat
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
  have hQfloor : Hprime/L^Cprime < (Q:ℝ)+1 := by
    simpa [hQ] using (Nat.lt_floor_add_one (Hprime/L^Cprime))
  have hHbound : Hprime ≤ ((Q:ℝ)+1)*L^Cprime := by
    exact (div_le_iff₀ hLpow).mp hQfloor.le
  have hDen : ((Q:ℝ)+1) ≤
      (((Q:ℝ)+1)*(r:ℝ))*|(k:ℝ)| := by
    calc
      (Q:ℝ)+1 = ((Q:ℝ)+1)*1 := by ring
      _ ≤ ((Q:ℝ)+1)*(r:ℝ) :=
        mul_le_mul_of_nonneg_left hrR hQ0.le
      _ ≤ ((Q:ℝ)+1)*(r:ℝ)*|(k:ℝ)| :=
        le_mul_of_one_le_right (by positivity) hkAbs
  have hArcDen : 1/((((Q:ℝ)+1)*(r:ℝ))*|(k:ℝ)|) ≤
      1/((Q:ℝ)+1) :=
    one_div_le_one_div_of_le hQ0 hDen
  have hArcScale : 1/((Q:ℝ)+1) ≤ L^Cprime/Hprime := by
    apply (div_le_div_iff₀ hQ0 hHp).mpr
    simpa [mul_comm] using hHbound
  calc
    (1/(((Q:ℝ)+1)*(r:ℝ)))/|(k:ℝ)| =
      1/((((Q:ℝ)+1)*(r:ℝ))*|(k:ℝ)|) := by
        simp only [div_eq_mul_inv, one_div, mul_inv_rev]
        ring
    _ ≤ 1/((Q:ℝ)+1) := hArcDen
    _ ≤ L^Cprime/Hprime := hArcScale
end Green64Analytic.CorrelationD

end

/-! ## SourceRationalArcUniformSaving -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1800000

/-- Sum the genuine per-center saving over the ORIGINAL rational centers.
Duplicate fractions and overlapping beta arcs do not require disjointness. -/
theorem source_rational_arc_uniform_saving434
    (Q : ℕ) (F : C(AddCircle (1:ℝ), ℂ)) (Hprime Carc Cexp A K L Y : ℝ)
    (hL : 1 ≤ L) (hC : 0 ≤ Cexp) (hK : 0 ≤ K) (hY : 0 ≤ Y)
    (hQ : (Q:ℝ) ≤ L^Cexp)
    (hArc : ∀ den h : ℕ, 0 < den → den ≤ Q → h < den →
      (∫ beta in {beta : ℝ | |beta| ≤ L^Carc/Hprime},
        ‖F (((h:ℝ)/(den:ℝ)+beta:ℝ):AddCircle (1:ℝ))‖^2) ≤ K*Y*L^(-A)) :
    (∑ center ∈ sourceRationalCenterSet Q,
      ∫ beta in {beta : ℝ | |beta| ≤ L^Carc/Hprime},
        ‖F ((center+beta:ℝ):AddCircle (1:ℝ))‖^2) ≤
      2*K*Y*L^(2*Cexp-A) := by
  classical
  have hLp : 0 < L := by linarith
  have hCenter (center : ℝ) (hc : center ∈ sourceRationalCenterSet Q) :
      (∫ beta in {beta : ℝ | |beta| ≤ L^Carc/Hprime},
        ‖F ((center+beta:ℝ):AddCircle (1:ℝ))‖^2) ≤ K*Y*L^(-A) := by
    obtain ⟨den,hden,hImage⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨h,hRange,heq⟩ := Finset.mem_image.mp hImage
    subst center
    exact hArc den h (by have := Finset.mem_range.mp hRange; omega)
      (by have := Finset.mem_range.mp hden; omega) (Finset.mem_range.mp hRange)
  have hCount : ((sourceRationalCenterSet Q).card:ℝ) ≤ 2*L^(2*Cexp) := by
    calc
      _ ≤ ((Q*(Q+1):ℕ):ℝ) := by exact_mod_cast source_rational_center_card_le Q
      _ ≤ _ := source_rational_center_polylog_budget Q L Cexp hL hC hQ
  calc
    _ ≤ ∑ center ∈ sourceRationalCenterSet Q, K*Y*L^(-A) :=
      Finset.sum_le_sum (fun center hc => hCenter center hc)
    _ = ((sourceRationalCenterSet Q).card:ℝ)*(K*Y*L^(-A)) := by simp
    _ ≤ (2*L^(2*Cexp))*(K*Y*L^(-A)) :=
      mul_le_mul_of_nonneg_right hCount (by positivity)
    _ = _ := by rw [show 2*Cexp-A = 2*Cexp+(-A) by ring,Real.rpow_add hLp]; ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCircleMajorArc -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 2500000

/-- Original rational major arcs on the normalized frequency circle. -/
def sourceCircleRationalArcs434 (Q : ℕ) (radius : ℝ) : Set (AddCircle (1:ℝ)) :=
  ⋃ center ∈ sourceRationalCenterSet Q,
    Metric.closedBall (center:AddCircle (1:ℝ)) radius

theorem source_circle_rational_arcs_measurable434 (Q : ℕ) (radius : ℝ) :
    MeasurableSet (sourceCircleRationalArcs434 Q radius) :=
  Finset.measurableSet_biUnion _ (fun _ _ => measurableSet_closedBall)

/-- Overlapping or wrapping major arcs are bounded by the sum of their
REAL beta-window energies. No disjointness or multiplicity assumption. -/
theorem source_circle_finite_union_energy434
    (F : C(AddCircle (1:ℝ),ℂ)) (centers : Finset ℝ) (radius : ℝ)
    (hr : 0 ≤ radius) (hrhalf : radius < 1/2) :
    (∫ θ in ⋃ c ∈ centers, Metric.closedBall (c:AddCircle (1:ℝ)) radius,
      ‖F θ‖^2 ∂AddCircle.haarAddCircle) ≤
    ∑ c ∈ centers, ∫ beta in {beta : ℝ | |beta| ≤ radius},
      ‖F ((c+beta:ℝ):AddCircle (1:ℝ))‖^2 := by
  classical
  let f : AddCircle (1:ℝ) → ℝ := fun θ => ‖F θ‖^2
  let arc := fun c : ℝ => Metric.closedBall (c:AddCircle (1:ℝ)) radius
  let major := ⋃ c ∈ centers, arc c
  have hMeas : MeasurableSet major :=
    Finset.measurableSet_biUnion _ (fun _ _ => measurableSet_closedBall)
  have hInt : Integrable f AddCircle.haarAddCircle := by
    have hc : Continuous f := (continuous_norm.comp F.continuous).pow 2
    simpa [IntegrableOn] using hc.continuousOn.integrableOn_compact
      (μ:=AddCircle.haarAddCircle) isCompact_univ
  have hNonneg (c : ℝ) (θ : AddCircle (1:ℝ)) : 0 ≤ (arc c).indicator f θ := by
    by_cases ht : θ ∈ arc c <;> simp [Set.indicator,ht,f,sq_nonneg]
  have hPoint (θ : AddCircle (1:ℝ)) :
      major.indicator f θ ≤ ∑ c ∈ centers, (arc c).indicator f θ := by
    by_cases ht : θ ∈ major
    · obtain ⟨c,hc,htc⟩ := Set.mem_iUnion₂.mp ht
      rw [Set.indicator_of_mem ht]
      calc
        f θ = (arc c).indicator f θ := (Set.indicator_of_mem htc f).symm
        _ ≤ ∑ c ∈ centers, (arc c).indicator f θ :=
          Finset.single_le_sum (fun c _ => hNonneg c θ) hc
    · rw [Set.indicator_of_notMem ht]
      exact Finset.sum_nonneg (fun c _ => hNonneg c θ)
  have hSumInt := integrable_finset_sum centers
    (fun c _ => hInt.indicator (measurableSet_closedBall (x:=(c:AddCircle (1:ℝ))) (ε:=radius)))
  calc
    _ = ∫ θ, major.indicator f θ ∂AddCircle.haarAddCircle :=
      (integral_indicator hMeas).symm
    _ ≤ ∫ θ, ∑ c ∈ centers, (arc c).indicator f θ ∂AddCircle.haarAddCircle :=
      integral_mono (hInt.indicator hMeas) hSumInt hPoint
    _ = ∑ c ∈ centers, ∫ θ, (arc c).indicator f θ ∂AddCircle.haarAddCircle :=
      integral_finset_sum centers (fun c _ => hInt.indicator measurableSet_closedBall)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [integral_indicator measurableSet_closedBall]
      exact source_circle_closed_ball_energy_eq_beta434 F c radius hr hrhalf

/-- Exact rational-center count combined with the actual real arc saving. -/
theorem source_circle_major_arc_saving434
    (Q : ℕ) (F : C(AddCircle (1:ℝ),ℂ)) (Hprime Carc Cexp A K L Y : ℝ)
    (hL : 1 ≤ L) (hC : 0 ≤ Cexp) (hK : 0 ≤ K) (hY : 0 ≤ Y)
    (hQ : (Q:ℝ) ≤ L^Cexp) (hr : 0 ≤ L^Carc/Hprime)
    (hrhalf : L^Carc/Hprime < 1/2)
    (hArc : ∀ den h : ℕ, 0 < den → den ≤ Q → h < den →
      (∫ beta in {beta : ℝ | |beta| ≤ L^Carc/Hprime},
        ‖F (((h:ℝ)/(den:ℝ)+beta:ℝ):AddCircle (1:ℝ))‖^2) ≤ K*Y*L^(-A)) :
    (∫ θ in sourceCircleRationalArcs434 Q (L^Carc/Hprime),
      ‖F θ‖^2 ∂AddCircle.haarAddCircle) ≤ 2*K*Y*L^(2*Cexp-A) :=
  (source_circle_finite_union_energy434 F (sourceRationalCenterSet Q) _ hr hrhalf).trans
    (source_rational_arc_uniform_saving434 Q F Hprime Carc Cexp A K L Y hL hC hK hY hQ hArc)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCircleRationalMembership -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 2500000

/-- Integer representatives disappear on the frequency circle. -/
theorem source_circle_integer_shift434 (theta : ℝ) (z : ℤ) :
    ((theta-(z:ℝ):ℝ):AddCircle (1:ℝ)) = (theta:AddCircle (1:ℝ)) := by
  have hz : ((z:ℝ):AddCircle (1:ℝ)) = 0 := by
    simpa only [zsmul_eq_mul,mul_one,AddCircle.coe_period,smul_zero] using
      (AddCircle.coe_zsmul (p:=(1:ℝ)) (n:=z) (x:=(1:ℝ)))
  rw [AddCircle.coe_sub,hz,sub_zero]

/-- The real representative inequality in the proved Dirichlet
partition implies membership in the actual closed circle major arc. -/
theorem source_circle_mem_ball_of_lift434 (theta center radius : ℝ) (z : ℤ)
    (h : |theta-(z:ℝ)-center| ≤ radius) :
    (theta:AddCircle (1:ℝ)) ∈ Metric.closedBall (center:AddCircle (1:ℝ)) radius := by
  rw [Metric.mem_closedBall,dist_eq_norm]
  have hCast : (theta:AddCircle (1:ℝ))-(center:AddCircle (1:ℝ)) =
      ((theta-(z:ℝ)-center:ℝ):AddCircle (1:ℝ)) := by
    rw [AddCircle.coe_sub,source_circle_integer_shift434]
  rw [hCast]
  exact (QuotientAddGroup.norm_mk_le_norm (S:=AddSubgroup.zmultiples (1:ℝ))).trans
    (by simpa only [Real.norm_eq_abs] using h)

theorem source_circle_rational_mem_of_lift434
    (Q q : ℕ) (h z : ℤ) (theta radius : ℝ)
    (hq : 0 < q) (hqQ : q ≤ Q) (hh0 : 0 ≤ h) (hhq : h < (q:ℤ))
    (hLift : |theta-(z:ℝ)-(h:ℝ)/(q:ℝ)| ≤ radius) :
    (theta:AddCircle (1:ℝ)) ∈ sourceCircleRationalArcs434 Q radius := by
  refine Set.mem_iUnion₂.mpr ⟨(h:ℝ)/(q:ℝ),?_,?_⟩
  · exact source_signed_rational_center_mem Q q h hq hqQ hh0 hhq
  · exact source_circle_mem_ball_of_lift434 theta _ radius z hLift
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCircleRationalArcInverseLift -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Real converse of SOURCE03 circle major-arc membership:
there is an ACTUAL allowed rational center and an
INTEGER period shift n with |theta-center-n|<=radius.
This is not a fabricated single shared center and does
not require radius<1/2: the exact AddCircle preimage
of a closed ball is the union over integral translates. -/
theorem source_circle_rational_arc_real_lift434
    (Q : ℕ) (theta radius : ℝ)
    (hMajor : (theta : AddCircle (1:ℝ)) ∈
      sourceCircleRationalArcs434 Q radius) :
    ∃ center ∈ sourceRationalCenterSet Q,
      ∃ n : ℤ, |theta - (center + (n:ℝ))| ≤ radius := by
  change (theta : AddCircle (1:ℝ)) ∈
    ⋃ center ∈ sourceRationalCenterSet Q,
      Metric.closedBall (center : AddCircle (1:ℝ)) radius
    at hMajor
  obtain ⟨center,hcenter,hBall⟩ := Set.mem_iUnion₂.mp hMajor
  have hPreimage :
      theta ∈ (fun t : ℝ => (t : AddCircle (1:ℝ))) ⁻¹'
        Metric.closedBall (center : AddCircle (1:ℝ)) radius :=
    hBall
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion
    (p := (1:ℝ)) center radius] at hPreimage
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hPreimage
  refine ⟨center,hcenter,n,?_⟩
  simpa only [Metric.mem_closedBall,
    Real.dist_eq, zsmul_eq_mul,mul_one] using hn
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCircleRationalArcFrequencyLift -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The ACTUAL original major-circle arc has a real lift with
a true allowed reduced-or-unreduced rational center h/q.
At physical frequency -(k:Real)*theta, the real Dirichlet
irrational remainder is -k*(theta-h/q-n), hence its radius
is multiplied by |k|. The real phase differs from
u/q+beta only by the INTEGER k*n; this is the periodic
integer-factor which must be handled in the physical
exponential bridge. No false omission of |k|. -/
theorem source_circle_rational_arc_frequency_real_lift434
    (Q : ℕ) (theta radius : ℝ) (k : ℤ)
    (hMajor : (theta : AddCircle (1:ℝ)) ∈
      sourceCircleRationalArcs434 Q radius) :
    ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧
      ∃ h : ℕ, h < q ∧
        ∃ n : ℤ, ∃ beta : ℝ,
          |beta| ≤ |(k:ℝ)| *radius ∧
          -(k:ℝ)*theta =
            (((-(k*(h:ℤ))):ℤ):ℝ)/(q:ℝ)
              + beta - ((k*n:ℤ):ℝ) := by
  classical
  obtain ⟨center,hcenter,n,hn⟩ :=
    source_circle_rational_arc_real_lift434
      Q theta radius hMajor
  obtain ⟨q,hq,hImage⟩ := Finset.mem_biUnion.mp hcenter
  obtain ⟨h,hh,heq⟩ := Finset.mem_image.mp hImage
  have hqpos : 0 < q := by
    have hhh := Finset.mem_range.mp hh
    omega
  have hqQ : q ≤ Q := by
    have hqq := Finset.mem_range.mp hq
    omega
  have hhq : h < q := Finset.mem_range.mp hh
  subst center
  let beta : ℝ := -(k:ℝ) *
    (theta - ((h:ℝ)/(q:ℝ) + (n:ℝ)))
  have hBeta : |beta| ≤ |(k:ℝ)| *radius := by
    calc
      |beta| =
          |(k:ℝ)| *|theta-((h:ℝ)/(q:ℝ)+(n:ℝ))| := by
            simp only [beta,abs_mul,abs_neg]
      _ ≤ |(k:ℝ)| *radius :=
        mul_le_mul_of_nonneg_left hn (abs_nonneg _)
  refine ⟨q,hqpos,hqQ,h,hhq,n,beta,hBeta,?_⟩
  dsimp only [beta]
  push_cast
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceFiniteComparisonSaving -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 4500000

/-- The actual finite comparison sum has arbitrary saving after the
original major-arc bounds and the independently proved multiplier estimate.
The displayed exponent choice includes the full rational-center count. -/
theorem source_finite_comparison_saving434 {ι : Type*}
    (J : Finset ι) (c : ι → ℂ) (shift : ι → ℤ)
    (S T : Finset ℤ) (a b : ℤ → ℂ) (Q : ℕ)
    (Hprime Carc Cexp Karc Kglobal Kminor Y L D E : ℝ)
    (hL : 1 ≤ L) (hCexp : 0 ≤ Cexp) (hKarc : 0 ≤ Karc)
    (hKglobal : 0 ≤ Kglobal) (hKminor : 0 ≤ Kminor) (hY : 0 ≤ Y)
    (hMass : (∑ j ∈ J, ‖c j‖) ≤ 1)
    (hQ : (Q:ℝ) ≤ L^Cexp) (hr : 0 ≤ L^Carc/Hprime)
    (hrhalf : L^Carc/Hprime < 1/2)
    (hFirst : (∑ n ∈ S, ‖a n‖^2) ≤ Kglobal*Y*L^E)
    (hSecond : (∑ n ∈ T, ‖b n‖^2) ≤ Kglobal*Y*L^E)
    (hArc : ∀ den h : ℕ, 0 < den → den ≤ Q → h < den →
      (∫ beta in {beta : ℝ | |beta| ≤ L^Carc/Hprime},
        ‖sourceCircleFourierPoly S a (((h:ℝ)/(den:ℝ)+beta:ℝ):AddCircle (1:ℝ))‖^2)
      ≤ Karc*Y*L^(-(2*Cexp+2*D+E)))
    (hMinor : ∀ θ ∉ sourceCircleRationalArcs434 Q (L^Carc/Hprime),
      ‖sourceFiniteShiftMultiplier434 J c shift θ‖ ≤ Kminor*L^(-D-E)) :
    ‖∑ j ∈ J, c j*(∑ m ∈ S, ∑ n ∈ T,
      if n = m+shift j then star (a m)*b n else 0)‖ ≤
      (Real.sqrt (2*Karc*Kglobal)+Kminor*Kglobal)*Y*L^(-D) := by
  let f := sourceCircleFourierPoly S a
  let g := sourceCircleFourierPoly T b
  let m := sourceFiniteShiftMultiplier434 J c shift
  let major := sourceCircleRationalArcs434 Q (L^Carc/Hprime)
  let delta := Kminor*L^(-D-E)
  have hLp : 0 < L := by linarith
  have hDelta : 0 ≤ delta := by dsimp [delta]; positivity
  have hf : MemLp f 2 AddCircle.haarAddCircle :=
    ContinuousMap.memLp (μ:=AddCircle.haarAddCircle) (p:=2) ℂ f
  have hg : MemLp g 2 AddCircle.haarAddCircle :=
    ContinuousMap.memLp (μ:=AddCircle.haarAddCircle) (p:=2) ℂ g
  have hBound : ∀ θ, ‖m θ‖ ≤ 1 := fun θ =>
    (source_finite_shift_multiplier_bound434 J c shift θ).trans hMass
  have hCauchy := source_comparison_major_minor434 AddCircle.haarAddCircle f g m major delta
    hf hg m.continuous.aestronglyMeasurable
    (source_circle_rational_arcs_measurable434 Q _) hDelta hBound hMinor
  have hMajor0 := source_circle_major_arc_saving434 Q f Hprime Carc Cexp
    (2*Cexp+2*D+E) Karc L Y hL hCexp hKarc hY hQ hr hrhalf hArc
  have hExponent : 2*Cexp-(2*Cexp+2*D+E) = -2*D-E := by ring
  rw [hExponent] at hMajor0
  have hF : (∫ θ, ‖f θ‖^2 ∂AddCircle.haarAddCircle) ≤ Kglobal*Y*L^E := by
    rw [show (∫ θ, ‖f θ‖^2 ∂AddCircle.haarAddCircle) = ∑ n ∈ S, ‖a n‖^2
      from source_circle_fourier_parseval S a]
    exact hFirst
  have hG : (∫ θ, ‖g θ‖^2 ∂AddCircle.haarAddCircle) ≤ Kglobal*Y*L^E := by
    rw [show (∫ θ, ‖g θ‖^2 ∂AddCircle.haarAddCircle) = ∑ n ∈ T, ‖b n‖^2
      from source_circle_fourier_parseval T b]
    exact hSecond
  have hSave := source_comparison_energy_budget434 _ _ _ _ delta
    (2*Karc) Kglobal Kminor Y L D E
    (integral_nonneg (fun θ => sq_nonneg ‖f θ‖))
    (integral_nonneg (fun θ => sq_nonneg ‖f θ‖))
    (integral_nonneg (fun θ => sq_nonneg ‖g θ‖))
    hDelta (by positivity) hKglobal hKminor hY hLp hMajor0 hF hG le_rfl hCauchy
  rw [source_finite_comparison_fourier_identity434] at hSave
  exact hSave
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueRationalCenterReduction -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The true rational center for Fourier frequency -k*theta
may initially have numerator u=-k*h and denominator q,
with gcd(u,q)>1 even if the original h/q was reduced.
This reduces that SAME rational center to coprime u'/q'
with 0<q'<=q, preserving its exact REAL value.
Thus the integer bilinear C196 estimate can use a true
coprime rational center without enlarging its denominator
or pretending gcd(k,q)=1. -/
theorem source_original_true_rational_center_reduce434
    (q : ℕ) (hq : 0 < q) (u : ℤ) :
    ∃ q' : ℕ, 0 < q' ∧ q' ≤ q ∧
      ∃ u' : ℤ, Nat.Coprime u'.natAbs q' ∧
        (u':ℝ)/(q':ℝ) = (u:ℝ)/(q:ℝ) := by
  classical
  let rat : ℚ := Rat.divInt u (q:ℤ)
  have hDenInt : (rat.den:ℤ) ∣ (q:ℤ) := by
    simpa only [rat] using Rat.den_dvd u (q:ℤ)
  have hDenNat : rat.den ∣ q :=
    Int.natCast_dvd_natCast.mp hDenInt
  have hDenPos : 0 < rat.den := rat.den_pos
  have hDenLe : rat.den ≤ q := Nat.le_of_dvd hq hDenNat
  have hRat :
      (rat.num:ℚ)/(rat.den:ℚ) = (u:ℚ)/(q:ℚ) := by
    have heq := Rat.num_divInt_den rat
    simpa only [Rat.divInt_eq_div, Int.cast_natCast, rat]
      using heq
  have hReal :
      (rat.num:ℝ)/(rat.den:ℝ) = (u:ℝ)/(q:ℝ) := by
    have hh := congrArg (fun z : ℚ => (z:ℝ)) hRat
    simpa only [Rat.cast_div, Rat.cast_intCast,
      Rat.cast_natCast] using hh
  exact ⟨rat.den,hDenPos,hDenLe,rat.num,rat.reduced,hReal⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceScaledExpChange -/

section

open MeasureTheory
open Set
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 700000

/-- The original log-center substitution v=Y exp u maps the full
real u-axis bijectively to the positive physical axis, for every Y>0. -/
theorem source_scaled_exp_range434 (Y : ℝ) (hY : 0 < Y) :
    Set.range (fun u : ℝ => Y * Real.exp u) = Set.Ioi 0 := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    exact mul_pos hY (Real.exp_pos u)
  · intro hv
    have hdiv : 0 < v/Y := div_pos hv hY
    refine ⟨Real.log (v/Y), ?_⟩
    change Y * Real.exp (Real.log (v/Y)) = v
    rw [Real.exp_log hdiv]
    exact mul_div_cancel₀ v hY.ne'

/-- Fully justified change of variables; the Jacobian Y exp u
is intrinsic to the original, not a source-energy input. -/
theorem source_scaled_exp_integral434
    (Y : ℝ) (hY : 0 < Y) (g : ℝ → ℝ) :
    (∫ v in Set.Ioi (0:ℝ), g v) =
      ∫ u : ℝ, (Y * Real.exp u) * g (Y * Real.exp u) := by
  let f : ℝ → ℝ := fun u => Y * Real.exp u
  have hd (u : ℝ) (_ : u ∈ Set.univ) :
      HasDerivWithinAt f (Y*Real.exp u) Set.univ u := by
    exact ((Real.hasDerivAt_exp u).const_mul Y).hasDerivWithinAt
  have hinj : Set.InjOn f Set.univ := by
    intro u _ w _ he
    have h : Real.exp u = Real.exp w :=
      mul_left_cancel₀ hY.ne' he
    exact Real.exp_injective h
  have he := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) (f := f) (f' := fun u => Y*Real.exp u)
    (g := g) MeasurableSet.univ hd hinj
  rw [Set.image_univ, source_scaled_exp_range434 Y hY] at he
  simpa only [f, setIntegral_univ, abs_of_pos (mul_pos hY (Real.exp_pos _)),
    smul_eq_mul] using he
end Green64Analytic.CorrelationSquare

end

/-! ## SourceScaledLogEnergy -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 850000

/-- Exact physical-to-logarithmic L² energy change at ORIGINAL v=Y exp u.
No integrability or source-saving is taken as a new hypothesis in
the algebraic Jacobian; source integrability is proven separately. -/
theorem source_scaled_log_energy434
    (Y : ℝ) (hY : 0 < Y) (Q : ℝ → ℂ) :
    (∫ v in Set.Ioi (0:ℝ), ‖Q (Real.log (v/Y))‖^2) =
      Y * (∫ u : ℝ, Real.exp u * ‖Q u‖^2) := by
  let g : ℝ → ℝ := fun v => ‖Q (Real.log (v/Y))‖^2
  have hchg := source_scaled_exp_integral434 Y hY g
  have hlog (u : ℝ) :
      Real.log ((Y*Real.exp u)/Y) = u := by
    have hy : Y ≠ 0 := hY.ne'
    have he : (Y*Real.exp u)/Y = Real.exp u := by
      field_simp
    rw [he, Real.log_exp]
  have hh (u : ℝ) :
      (Y*Real.exp u) * g (Y*Real.exp u) =
      Y * (Real.exp u * ‖Q u‖^2) := by
    dsimp [g]
    rw [hlog u]
    ring
  calc
    _ = ∫ u : ℝ, (Y*Real.exp u)*g (Y*Real.exp u) := hchg
    _ = ∫ u : ℝ, Y*(Real.exp u*‖Q u‖^2) := by
      apply integral_congr_ae
      filter_upwards with u
      exact hh u
    _ = _ := integral_const_mul _ _
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalWeightedLog -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 900000

/-- Source compact support makes the Jacobian exp(u) harmless,
with a constant exp(B) and NOT an unproved energy saving. -/
theorem source_compact_exp_weight_integrable434
    (Q : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hQ : Continuous Q)
    (hSq : Integrable (fun u : ℝ => ‖Q u‖^2))
    (hSupport : ∀ u ∉ Set.Icc (-B) B, Q u = 0) :
    Integrable (fun u : ℝ => Real.exp u * ‖Q u‖^2) := by
  have hm : AEStronglyMeasurable
      (fun u : ℝ => Real.exp u * ‖Q u‖^2) :=
    (Real.continuous_exp.mul (hQ.norm.pow 2)).aestronglyMeasurable
  apply Integrable.mono' (hSq.const_mul (Real.exp B)) hm
  filter_upwards with u
  by_cases hu : u ∈ Set.Icc (-B) B
  · have hle : Real.exp u ≤ Real.exp B :=
      Real.exp_le_exp.mpr (Set.mem_Icc.mp hu).2
    have hh : 0 ≤ Real.exp u * ‖Q u‖^2 := by positivity
    change |Real.exp u * ‖Q u‖^2| ≤ Real.exp B * ‖Q u‖^2
    rw [abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  · have hz := hSupport u hu
    simp [hz]

/-- Apply the previous generic Jacobian-integrability lemma to
the ACTUAL original source physical Q_h. -/
theorem source_actual_physical_exp_weight_integrable434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M) :
    Integrable (fun u : ℝ =>
      Real.exp u * ‖sourceActualPhysicalQ434 chi kappa h P u‖^2) := by
  have hc := source_actual_physical_Q_continuous_native434
    chi kappa B hB hchi j hj h hh P hP M hM hBound
  have hSq := source_actual_physical_Q_sq_integrable434
    chi kappa B hB hchi j hj h hh P hP M hM hBound
  have hs : ∀ u ∉ Set.Icc (-B) B,
      sourceActualPhysicalQ434 chi kappa h P u = 0 := by
    intro u hu
    exact source_actual_physical_Q_support434 chi kappa B hchi h P u hu
  exact source_compact_exp_weight_integrable434
    (sourceActualPhysicalQ434 chi kappa h P) B hB.le hc hSq hs
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalExactNormalization -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 800000

/-- Exact original physical collar L² normalization after v=Y exp u:
the full v-measure Jacobian and angular H/(2πv) leave precisely
1/Y times (2π)^(-2). No 1/H², Y² or residual H factor is omitted. -/
theorem source_physical_normalized_log_energy434
    (H Y : ℝ) (hH : 0 < H) (hY : 0 < Y) (Q : ℝ → ℂ) :
    (H^2)⁻¹ *
      (∫ v in Set.Ioi (0:ℝ),
        (H/(2*Real.pi*Y))^2 * ‖Q (Real.log (v/Y))‖^2) =
      ((1/Y)*(1/(2*Real.pi)^2)) *
        (∫ u : ℝ, Real.exp u * ‖Q u‖^2) := by
  have hchange := source_scaled_log_energy434 Y hY Q
  have hnorm := source_physical_one_over_Y_2pi434 H Y hH hY
  calc
    _ = ((H^2)⁻¹) * (H/(2*Real.pi*Y))^2 *
          (∫ v in Set.Ioi (0:ℝ),
            ‖Q (Real.log (v/Y))‖^2) := by
      rw [integral_const_mul]
      ring
    _ = ((H^2)⁻¹)*(H/(2*Real.pi*Y))^2*
          (Y*(∫ u : ℝ, Real.exp u*‖Q u‖^2)) := by
      rw [hchange]
    _ = (((Y/H^2)*(H/(2*Real.pi*Y))^2)) *
          (∫ u : ℝ, Real.exp u*‖Q u‖^2) := by ring
    _ = _ := by rw [hnorm]
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalExpMassBound -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 850000

/-- A genuine original compact log-center support bound, without
using Fourier estimates or hiding an h-dependent constant. -/
theorem source_compact_exp_mass_le434
    (Q : ℝ → ℂ) (B : ℝ)
    (hSupport : ∀ u ∉ Set.Icc (-B) B, Q u = 0)
    (hSq : Integrable (fun u : ℝ => ‖Q u‖^2))
    (hExp : Integrable (fun u : ℝ => Real.exp u * ‖Q u‖^2)) :
    (∫ u : ℝ, Real.exp u * ‖Q u‖^2) ≤
      Real.exp B * (∫ u : ℝ, ‖Q u‖^2) := by
  calc
    _ ≤ ∫ u : ℝ, Real.exp B * ‖Q u‖^2 := by
      apply integral_mono hExp (hSq.const_mul (Real.exp B))
      intro u
      by_cases hu : u ∈ Set.Icc (-B) B
      · exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (Set.mem_Icc.mp hu).2) (sq_nonneg _)
      · change Real.exp u * ‖Q u‖^2 ≤ Real.exp B * ‖Q u‖^2
        rw [hSupport u hu]
        norm_num
    _ = _ := integral_const_mul _ _

/-- Exact physical original-energy mass after logarithmic substitution
is bounded by e^B/Y times the original Q L² energy, with angular factor.
No physical Fourier Parseval theorem is assumed in this geometry lemma. -/
theorem source_actual_physical_log_energy_geometry434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M)
    (H Y : ℝ) (hH : 0 < H) (hY : 0 < Y) :
    (H^2)⁻¹ *
      (∫ v in Set.Ioi (0:ℝ),
        (H/(2*Real.pi*Y))^2 *
        ‖sourceActualPhysicalQ434 chi kappa h P
          (Real.log (v/Y))‖^2) ≤
      ((1/Y)*(1/(2*Real.pi)^2)) * Real.exp B *
        (∫ u : ℝ, ‖sourceActualPhysicalQ434 chi kappa h P u‖^2) := by
  let Q := sourceActualPhysicalQ434 chi kappa h P
  have hSq := source_actual_physical_Q_sq_integrable434
    chi kappa B hB hchi j hj h hh P hP M hM hBound
  have hExp := source_actual_physical_exp_weight_integrable434
    chi kappa B hB hchi j hj h hh P hP M hM hBound
  have hs (u : ℝ) (hu : u ∉ Set.Icc (-B) B) : Q u = 0 :=
    source_actual_physical_Q_support434 chi kappa B hchi h P u hu
  have hmass := source_compact_exp_mass_le434 Q B hs hSq hExp
  have hcoef : 0 ≤ ((1/Y)*(1/(2*Real.pi)^2)) := by positivity
  calc
    _ = ((1/Y)*(1/(2*Real.pi)^2)) *
          (∫ u : ℝ, Real.exp u * ‖Q u‖^2) :=
      source_physical_normalized_log_energy434 H Y hH hY Q
    _ ≤ ((1/Y)*(1/(2*Real.pi)^2)) *
          (Real.exp B * ∫ u : ℝ, ‖Q u‖^2) :=
      mul_le_mul_of_nonneg_left hmass hcoef
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualPhysicalNormalizedL2 -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1600000

/-- Source ACTUAL full physical collar estimate at the exact h=H/Y scale:
normalized physical v-energy ≤ (fixed C/Y) times the genuine
all-real Mellin weighted second moment. C is UNIFORM in H,Y,P and all
source labels, with no source energy-saving assumption. -/
theorem source_actual_physical_normalized_L2_schur434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (H Y : ℝ), 0 < H → 0 < Y →
      ∀ (P : ℝ → ℂ) (hP : Continuous P)
        (M : ℝ), 0 ≤ M → (∀ t, ‖P t‖ ≤ M) →
        (H^2)⁻¹ *
          (∫ v in Set.Ioi (0:ℝ),
            (H/(2*Real.pi*Y))^2 *
            ‖sourceActualPhysicalQ434 chi kappa (H/Y) P
              (Real.log (v/Y))‖^2) ≤
          (K/Y) * (∫ t : ℝ,
            ((1+(H/Y)*|t|)^j)⁻¹ * ‖P t‖^2) := by
  obtain ⟨C,hC,hSchur⟩ :=
    source_actual_physical_Q_L2_schur434 chi kappa B hB hchi j hj
  let mass : ℝ := ∫ s : ℝ, collarSchurWeight434 s
  let A : ℝ :=
    (1/(2*Real.pi)^2) * Real.exp B * C^2 *
      (2*Real.pi) * mass^2
  let K : ℝ := A+1
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hK : 0 < K := by dsimp [K]; linarith
  refine ⟨K,hK,?_⟩
  intro H Y hH hY P hP M hM hBound
  have hh : 0 < H/Y := div_pos hH hY
  let Q : ℝ → ℂ := sourceActualPhysicalQ434 chi kappa (H/Y) P
  let E : ℝ := ∫ t : ℝ, ((1+(H/Y)*|t|)^j)⁻¹ * ‖P t‖^2
  let G : ℝ := ((1/Y)*(1/(2*Real.pi)^2))*Real.exp B
  have hE : 0 ≤ E := integral_nonneg (fun t => by
    apply mul_nonneg
    · exact (source_collar_real_weight_le_one434
        (H/Y) t hh.le j).1
    · positivity)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hGeo := source_actual_physical_log_energy_geometry434
    chi kappa B hB hchi j hj (H/Y) hh
    P hP M hM hBound H Y hH hY
  have hQ := hSchur (H/Y) hh P hP M hM hBound
  calc
    _ ≤ G * (∫ u : ℝ, ‖Q u‖^2) := hGeo
    _ ≤ G * (C^2*(2*Real.pi)*mass^2*E) :=
      mul_le_mul_of_nonneg_left hQ hG
    _ = (A/Y)*E := by
      dsimp [G,A]
      ring
    _ ≤ (K/Y)*E := by
      have hAK : A ≤ K := by dsimp [K]; linarith
      have hdiv : A/Y ≤ K/Y :=
        (div_le_div_of_nonneg_right hAK hY.le)
      exact mul_le_mul_of_nonneg_right hdiv hE
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralFinitePhase -/

section

open MeasureTheory
open scoped SchwartzMap BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1000000

/-- Byte-for-byte sourcePhase formula from SourceRealFrequencyPhases:
I*t*log n, including n=0. This is a local exact-formula bridge pending
native import of the original named sourcePhase declaration. -/
noncomputable def sourceLiteralMellinPhase434 (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ))

theorem source_literal_phase_continuous434 (n : ℕ) :
    Continuous (sourceLiteralMellinPhase434 n) := by
  unfold sourceLiteralMellinPhase434
  fun_prop

theorem source_literal_phase_norm434 (n : ℕ) (t : ℝ) :
    ‖sourceLiteralMellinPhase434 n t‖ = 1 := by
  unfold sourceLiteralMellinPhase434
  rw [Complex.norm_exp]
  have hre : (Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ)).re = 0 := by
    rw [Complex.mul_re]
    simp only [Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_self]
  rw [hre, Real.exp_zero]
/-- The same ordinary finite Mellin series used at the original four-factor
source endpoint; the coefficient function is left untouched. -/
noncomputable def sourceLiteralFiniteMellin434
    (F : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ F, a n * sourceLiteralMellinPhase434 n t

theorem source_literal_finite_mellin_continuous434
    (F : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (sourceLiteralFiniteMellin434 F a) := by
  unfold sourceLiteralFiniteMellin434
  apply continuous_finsetSum F
  intro n hn
  exact continuous_const.mul (source_literal_phase_continuous434 n)

theorem source_literal_finite_mellin_uniform434
    (F : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖sourceLiteralFiniteMellin434 F a t‖ ≤ ∑ n ∈ F, ‖a n‖ := by
  unfold sourceLiteralFiniteMellin434
  calc
    _ ≤ ∑ n ∈ F, ‖a n * sourceLiteralMellinPhase434 n t‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ F, ‖a n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, source_literal_phase_norm434, mul_one]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralFiniteEnergy -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 950000

/-- Original formula finite Mellin polynomial has genuine all-real-time
weighted L² integrability for j>=2; not an assumed energy saving. -/
theorem source_literal_finite_mellin_weighted_integrable434
    (F : Finset ℕ) (a : ℕ → ℂ) (h : ℝ) (hh : 0 < h)
    (j : ℕ) (hj : 2 ≤ j) :
    Integrable (fun t : ℝ =>
      ((1+h*|t|)^j)⁻¹ * ‖sourceLiteralFiniteMellin434 F a t‖^2) := by
  let M : ℝ := ∑ n ∈ F, ‖a n‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  exact source_real_time_bounded_energy_integrable434 h hh j hj
    (sourceLiteralFiniteMellin434 F a)
    (source_literal_finite_mellin_continuous434 F a)
    M hM (source_literal_finite_mellin_uniform434 F a)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualFullTimeLowHighSplit -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 900000

/-- Completely honest real-time low/high split of the source collar
weight for the ORIGINAL finite Mellin polynomial:
the low band incurs no weight loss (w≤1), the high band is the
actual WHOLE real integral over |t|≥T. The split costs no
source-saving or pre-assumed tail estimate. -/
theorem source_original_real_time_weight_low_high434
    (F : Finset ℕ) (a : ℕ → ℂ)
    (h : ℝ) (hh : 0 < h) (j : ℕ) (hj : 2 ≤ j)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t : ℝ,
      ((1+h*|t|)^j)⁻¹ *
        ‖sourceLiteralFiniteMellin434 F a t‖^2) ≤
      (∫ t in Set.Icc (-T) T,
        ‖sourceLiteralFiniteMellin434 F a t‖^2) +
      (∫ t in {t : ℝ | T ≤ |t|},
        ((1+h*|t|)^j)⁻¹ *
          ‖sourceLiteralFiniteMellin434 F a t‖^2) := by
  let P : ℝ → ℂ := sourceLiteralFiniteMellin434 F a
  let f : ℝ → ℝ := fun t =>
    ((1+h*|t|)^j)⁻¹ * ‖P t‖^2
  let S : Set ℝ := Set.Icc (-T) T
  let Hi : Set ℝ := {t : ℝ | T ≤ |t|}
  have hInt : Integrable f :=
    source_literal_finite_mellin_weighted_integrable434 F a h hh j hj
  have hPCont : Continuous (fun t : ℝ => ‖P t‖^2) :=
    (source_literal_finite_mellin_continuous434 F a).norm.pow 2
  have hLoInt : IntegrableOn (fun t : ℝ => ‖P t‖^2) S :=
    hPCont.integrableOn_Icc
  have hLo : (∫ t in S, f t) ≤
      (∫ t in S, ‖P t‖^2) := by
    apply setIntegral_mono_on
      (hInt.mono_measure Measure.restrict_le_self)
      hLoInt measurableSet_Icc
    intro t ht
    simpa only [f, one_mul] using
      (mul_le_mul_of_nonneg_right
        (source_collar_real_weight_le_one434 h t hh.le j).2
        (sq_nonneg ‖P t‖))
  have hSub : Sᶜ ⊆ Hi := by
    intro t ht
    have hn : ¬ (-T ≤ t ∧ t ≤ T) := by
      simpa only [S, Set.mem_compl_iff, Set.mem_Icc] using ht
    rcases (not_and_or.mp hn) with hnlow | hnhigh
    · have hlt : t < -T := lt_of_not_ge hnlow
      exact (by
        dsimp [Hi]
        calc T ≤ -t := by linarith
             _ ≤ |t| := neg_le_abs t)
    · have hgt : T < t := lt_of_not_ge hnhigh
      exact (by
        dsimp [Hi]
        exact (le_of_lt hgt).trans (le_abs_self t))
  have hNonneg (t : ℝ) : 0 ≤ f t := by
    dsimp [f]
    exact mul_nonneg
      (source_collar_real_weight_le_one434 h t hh.le j).1
      (sq_nonneg _)
  have hHi : (∫ t in Sᶜ, f t) ≤
      (∫ t in Hi, f t) := by
    apply setIntegral_mono_set
      (hInt.mono_measure Measure.restrict_le_self)
      (Filter.Eventually.of_forall hNonneg)
    exact Filter.Eventually.of_forall (fun t ht => hSub ht)
  have hSplit : (∫ t : ℝ, f t) =
      (∫ t in S, f t) + (∫ t in Sᶜ, f t) :=
    (integral_add_compl measurableSet_Icc hInt).symm
  change (∫ t : ℝ, f t) ≤
    (∫ t in S, ‖P t‖^2) + (∫ t in Hi, f t)
  calc
    _ = (∫ t in S, f t) + (∫ t in Sᶜ, f t) := hSplit
    _ ≤ (∫ t in S, ‖P t‖^2) + (∫ t in Hi, f t) :=
      add_le_add hLo hHi
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralDyadicShell -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1250000

/-- Kernel-definitional match with the already checked source continuous
mean-square estimate: I*t*log(n) and (t*log n)*I are identical. -/
theorem source_literal_phase_matches_mean_square434 (n : ℕ) (t : ℝ) :
    sourceLiteralMellinPhase434 n t =
      Complex.exp (((t*Real.log (n : ℝ):ℝ):ℂ) * Complex.I) := by
  unfold sourceLiteralMellinPhase434
  rw [mul_comm Complex.I]

theorem source_literal_finite_matches_mean_square434
    (F : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    sourceLiteralFiniteMellin434 F a t =
      ∑ n ∈ F, a n *
        Complex.exp (((t*Real.log (n : ℝ):ℝ):ℂ) * Complex.I) := by
  unfold sourceLiteralFiniteMellin434
  apply Finset.sum_congr rfl
  intro n hn
  rw [source_literal_phase_matches_mean_square434]
/-- Exact finite-source real-time L² mean square, with no artificial
source saving, valid for both positive and negative endpoints. -/
theorem source_literal_mean_square_interval434
    (N : ℕ) (F : Finset ℕ) (a : ℕ → ℂ)
    (t0 t1 : ℝ) (hF : F ⊆ Finset.Icc 1 N) (ht : t0 ≤ t1) :
    (∫ t in Set.Icc t0 t1, ‖sourceLiteralFiniteMellin434 F a t‖^2) ≤
      ((t1-t0)+16*(N:ℝ)*(1+Real.log N)) *
        ∑ n ∈ F, ‖a n‖^2 := by
  have hh := Green64Analytic.Correlation.continuousMeanSquare
    N F a t0 t1 hF ht
  have he (t : ℝ) :
      ‖sourceLiteralFiniteMellin434 F a t‖^2 =
        ‖∑ n ∈ F, a n *
          Complex.exp (((t*Real.log (n : ℝ):ℝ):ℂ)*Complex.I)‖^2 := by
    rw [source_literal_finite_matches_mean_square434]
  simpa only [he] using hh

/-- Both source dyadic halves are controlled by the same genuine
coefficient square norm, with no condition on sign or t-shifts. -/
theorem source_literal_dyadic_two_sides434
    (N : ℕ) (F : Finset ℕ) (a : ℕ → ℂ)
    (R : ℝ) (hR : 0 ≤ R) (hF : F ⊆ Finset.Icc 1 N) :
    (∫ t in Set.Icc R (2*R), ‖sourceLiteralFiniteMellin434 F a t‖^2) ≤
      (R+16*(N:ℝ)*(1+Real.log N))*∑ n ∈ F, ‖a n‖^2 ∧
    (∫ t in Set.Icc (-2*R) (-R),
      ‖sourceLiteralFiniteMellin434 F a t‖^2) ≤
      (R+16*(N:ℝ)*(1+Real.log N))*∑ n ∈ F, ‖a n‖^2 := by
  constructor
  · have hp := source_literal_mean_square_interval434 N F a
      R (2*R) hF (by linarith)
    convert hp using 1 <;> ring
  · have hn := source_literal_mean_square_interval434 N F a
      (-2*R) (-R) hF (by linarith)
    convert hn using 1 <;> ring

/-- The complete paired source shell bound, before applying the
j>=2 collar time weight. -/
theorem source_literal_dyadic_paired434
    (N : ℕ) (F : Finset ℕ) (a : ℕ → ℂ)
    (R : ℝ) (hR : 0 ≤ R) (hF : F ⊆ Finset.Icc 1 N) :
    (∫ t in Set.Icc R (2*R), ‖sourceLiteralFiniteMellin434 F a t‖^2) +
      (∫ t in Set.Icc (-2*R) (-R),
      ‖sourceLiteralFiniteMellin434 F a t‖^2) ≤
      2 * (R+16*(N:ℝ)*(1+Real.log N)) *
        ∑ n ∈ F, ‖a n‖^2 := by
  obtain ⟨hp,hn⟩ := source_literal_dyadic_two_sides434 N F a R hR hF
  linarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralTruncateReal -/

section

open scoped BigOperators

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 380000

/-- Remove the artificial bookkeeping cutoff N from the TRUE finite
source Mellin polynomial whenever its actual coefficient vanishes
outside the physical cutoff M. No new coefficient data are introduced. -/
theorem source_literal_finite_mellin_truncate434
    (N M : ℕ) (a : ℕ → ℂ)
    (hZero : ∀ n ∈ Finset.Icc 1 N, M < n → a n = 0)
    (t : ℝ) :
    sourceLiteralFiniteMellin434 (Finset.Icc 1 N) a t =
      sourceLiteralFiniteMellin434 (Finset.Icc 1 (min N M)) a t := by
  let F : Finset ℕ := Finset.Icc 1 N
  let F' : Finset ℕ := Finset.Icc 1 (min N M)
  have hsub : F' ⊆ F := by
    intro n hn
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hn).1,
       (Finset.mem_Icc.mp hn).2.trans (min_le_left N M)⟩
  have hAway (n : ℕ) (hFn : n ∈ F) (hnot : n ∉ F') :
      M < n := by
    have hN : n ≤ N := (Finset.mem_Icc.mp hFn).2
    by_contra hh
    have hM : n ≤ M := Nat.le_of_not_gt hh
    exact hnot (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hFn).1,
       le_min hN hM⟩)
  unfold sourceLiteralFiniteMellin434
  exact (Finset.sum_subset hsub
    (fun n hn hnot => by
      have hz := hZero n hn (hAway n hn hnot)
      simp [hz])).symm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralTwisted -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 800000

/-- Exact source common physical phase exp(-it log Y), not a new parity
or Dirichlet twist. The source coefficient function is unchanged. -/
noncomputable def sourceLiteralTwistedMellin434
    (Y : ℝ) (F : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  Complex.exp (((-t*Real.log Y : ℝ):ℂ)*Complex.I) *
    sourceLiteralFiniteMellin434 F a t

theorem source_literal_twisted_continuous434
    (Y : ℝ) (F : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (sourceLiteralTwistedMellin434 Y F a) := by
  have hphase : Continuous (fun t : ℝ =>
      Complex.exp (((-t*Real.log Y : ℝ):ℂ)*Complex.I)) := by
    fun_prop
  unfold sourceLiteralTwistedMellin434
  exact hphase.mul (source_literal_finite_mellin_continuous434 F a)
theorem source_literal_twisted_norm434
    (Y : ℝ) (F : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖sourceLiteralTwistedMellin434 Y F a t‖ =
      ‖sourceLiteralFiniteMellin434 F a t‖ := by
  unfold sourceLiteralTwistedMellin434
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem source_literal_twisted_bound434
    (Y : ℝ) (F : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖sourceLiteralTwistedMellin434 Y F a t‖ ≤ ∑ n ∈ F, ‖a n‖ := by
  rw [source_literal_twisted_norm434]
  exact source_literal_finite_mellin_uniform434 F a t
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralPhysicalNormalized -/

section

open MeasureTheory
open scoped SchwartzMap BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1300000

/-- Normalized ORIGINAL compact-center physical operator, now
specialized to an arbitrary finite Mellin polynomial with EXACT
source phase I*t*log n and unchanged common phase e^{-it log Y}.
This does not yet identify a with the frozen marked coefficient. -/
theorem source_literal_finite_physical_normalized434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (H Y : ℝ), 0 < H → 0 < Y →
      ∀ (F : Finset ℕ) (a : ℕ → ℂ),
        (H^2)⁻¹ *
          (∫ v in Set.Ioi (0:ℝ),
            (H/(2*Real.pi*Y))^2 *
            ‖sourceActualPhysicalQ434 chi kappa (H/Y)
              (sourceLiteralTwistedMellin434 Y F a)
              (Real.log (v/Y))‖^2) ≤
        (K/Y) * (∫ t : ℝ,
          ((1+(H/Y)*|t|)^j)⁻¹ *
          ‖sourceLiteralFiniteMellin434 F a t‖^2) := by
  obtain ⟨K,hK,hphysical⟩ :=
    source_actual_physical_normalized_L2_schur434
      chi kappa B hB hchi j hj
  refine ⟨K,hK,?_⟩
  intro H Y hH hY F a
  let M : ℝ := ∑ n ∈ F, ‖a n‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have htwisted := hphysical H Y hH hY
    (sourceLiteralTwistedMellin434 Y F a)
    (source_literal_twisted_continuous434 Y F a)
    M hM (source_literal_twisted_bound434 Y F a)
  simpa only [source_literal_twisted_norm434] using htwisted
end Green64Analytic.CorrelationSquare

end

