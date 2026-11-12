module

public import Green64.Library.Weights.SourceD61CenteredBilinear
public import Green64.Library.Weights.Part012
public import Mathlib
public import Green64.Library.Weights.Part011

@[expose] public section

/-!
# Weights / Part013

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceD61ActualFullCellMixed -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Literal D20 FULL-cell signed coefficient, not a shortened divisor
fibre or a new hypothetical centered alpha. For every complex actual
D61 kernel H (including P/character/Fourier masks), the full double
Delta sum is EXACTLY its mixed second difference over the original
complete logarithmic cofactor cells. This is an identity, not a smallness
bound on that second difference. -/
theorem source_D20_full_cell_complex_mixed_difference434
    (Δ W y : ℝ) (hΔ : 0 < Δ) (hWy : W ≤ y)
    (j₁ j₂ : ℕ) (m₀ t₀ : ℕ) (H : ℕ → ℕ → ℂ) :
    (∑ m ∈ sourceD20LogCell Δ j₁,
      ∑ t ∈ sourceD20LogCell Δ j₂,
        (sourceD20FullDelta Δ W y m : ℂ) *
        (sourceD20FullDelta Δ W y t : ℂ) * H m t) =
    ∑ m ∈ sourceD20LogCell Δ j₁,
      ∑ t ∈ sourceD20LogCell Δ j₂,
        (sourceD20FullDelta Δ W y m : ℂ) *
        (sourceD20FullDelta Δ W y t : ℂ) *
          (H m t-H m t₀-H m₀ t+H m₀ t₀) := by
  have h₁ : (∑ m ∈ sourceD20LogCell Δ j₁,
      (sourceD20FullDelta Δ W y m : ℂ)) = 0 := by
    exact_mod_cast sourceD20_full_delta_zero hΔ hWy j₁
  have h₂ : (∑ t ∈ sourceD20LogCell Δ j₂,
      (sourceD20FullDelta Δ W y t : ℂ)) = 0 := by
    exact_mod_cast sourceD20_full_delta_zero hΔ hWy j₂
  exact centered_complex_bilinear_mixed_difference434
    (sourceD20LogCell Δ j₁) (sourceD20LogCell Δ j₂)
    (fun m => (sourceD20FullDelta Δ W y m : ℂ))
    (fun t => (sourceD20FullDelta Δ W y t : ℂ)) h₁ h₂ m₀ t₀ H
end Green64ComparisonPartial

end

end

/-! ## SourceNativeRAWJRatioPolynomial -/

section

open Filter Real
noncomputable section
namespace Green64ComparisonPartial
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Explicit original all-J BIG collision boost is LOGARITHMIC-power,
not exponential in L. For fixed source tmax and original BIG group
count O(log L), 1+2^(2 J |BIG|) is bounded by L^E with
E=1+2*tmax*Cg*log(2). Hence any target saving L^-D is obtained by
asking the already proved source shared-defect theorem at D+E. -/
theorem original_RAW_J_boost_polynomial434
    (L Cg : ℝ) (J tmax N : ℕ)
    (hL : 2 ≤ L) (hCg : 0 ≤ Cg)
    (hJ : J ≤ tmax)
    (hN : (N:ℝ) ≤ Cg * Real.log L) :
    1+(2:ℝ)^(2*J*N) ≤
      L^(1+2*(tmax:ℝ)*Cg*Real.log 2) := by
  have hLpos : 0 < L := by linarith
  have hLog : 0 ≤ Real.log L :=
    Real.log_nonneg (by linarith)
  have h2 : 0 < Real.log (2:ℝ) :=
    Real.log_pos (by norm_num)
  let E : ℝ := 2*(tmax:ℝ)*Cg*Real.log 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hJreal : (J:ℝ) ≤ (tmax:ℝ) := by exact_mod_cast hJ
  have hFirst : ((2*J*N:ℕ):ℝ) ≤ 2*(tmax:ℝ)*(N:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hJreal
      (Nat.cast_nonneg N : (0:ℝ) ≤ N)
    push_cast
    nlinarith [h]
  have hSecond : 2*(tmax:ℝ)*(N:ℝ) ≤
      2*(tmax:ℝ)*(Cg*Real.log L) := by
    exact mul_le_mul_of_nonneg_left hN (by positivity)
  have hExp : ((2*J*N:ℕ):ℝ)*Real.log 2 ≤
      E*Real.log L := by
    have h := mul_le_mul_of_nonneg_right (hFirst.trans hSecond) h2.le
    dsimp [E]
    nlinarith [h]
  have hPow : (2:ℝ)^(2*J*N) ≤ L^E := by
    calc
      _ = Real.exp (((2*J*N:ℕ):ℝ)*Real.log 2) := by
        rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
      _ ≤ Real.exp (E*Real.log L) := Real.exp_le_exp.mpr hExp
      _ = L^E := by
        rw [Real.rpow_def_of_pos hLpos]
        ring
  have hOne : 1 ≤ L^E :=
    Real.one_le_rpow (by linarith) hE
  calc
    1+(2:ℝ)^(2*J*N) ≤ 2*L^E := by linarith
    _ ≤ L*L^E := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hLpos.le E)
    _ = L^(1+2*(tmax:ℝ)*Cg*Real.log 2) := by
      dsimp [E]
      rw [Real.rpow_add hLpos,Real.rpow_one]
end Green64ComparisonPartial

end

end

/-! ## SourceNonexceptionalNumeric -/

section

namespace Green64Analytic.CorrelationMellin

/-! Quantitative small-prime saving. All assumptions here are explicit
source-scale inequalities; nothing about an exceptional set or an
unproved mean square is assumed. The constant 40 absorbs the actual
fixed threefold divisor moment and continuous mean-square overhead. -/

theorem source_nonexceptional_polylog_crush
    (L T U W B : ℝ) (E D : ℕ)
    (hL : 3 ≤ L) (hU : 0 < U) (hTU : T ≤ U)
    (hW : 1 ≤ W) (hWmax : W ≤ L^2)
    (hB : 0 ≤ B) (hBmax : B ≤ L^E) :
    ((L^(E+D+40))⁻¹)^2 *
      ((2*T+128*U*W) * (B^2/U * W^16)) ≤
      (L^D)⁻¹ := by
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hUW : U ≤ U*W := by
    nlinarith [mul_nonneg (le_of_lt hU) (sub_nonneg.mpr hW)]
  have hPref : 2*T+128*U*W ≤ 130*U*W := by
    nlinarith
  have h130 : (130:ℝ) ≤ L^5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hL 5
    norm_num at h
    linarith
  have hW17 : W^17 ≤ (L^2)^17 :=
    pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ W) hWmax 17
  have h39 : 130*W^17 ≤ L^39 := by
    calc
      _ ≤ L^5 * (L^2)^17 :=
        mul_le_mul h130 hW17 (pow_nonneg (by linarith : 0 ≤ W) _)
          (pow_nonneg hLpos.le _)
      _ = L^39 := by
        rw [←pow_mul, ←pow_add]
  have hB2 : B^2 ≤ (L^E)^2 :=
    (sq_le_sq₀ hB (by positivity)).mpr hBmax
  have hPowerLHS :
      (L^E)^2 * L^39 * L^D ≤ (L^(E+D+40))^2 := by
    have hp : L^(2*E+39+D) ≤ L^(2*(E+D+40)) :=
      pow_le_pow_right₀ hLone (by omega)
    have hlhs : (L^E)^2 * L^39 * L^D =
        L^(2*E+39+D) := by
      rw [←pow_mul, ←pow_add, ←pow_add]
      congr 1
      omega
    have hrhs : (L^(E+D+40))^2 =
        L^(2*(E+D+40)) := by
      rw [←pow_mul]
      congr 1
      omega
    rwa [hlhs,hrhs]
  have hPower :
      ((L^(E+D+40))⁻¹)^2 * ((L^E)^2 * L^39) ≤
        (L^D)⁻¹ := by
    have hDiv :
        ((L^E)^2*L^39)/(L^(E+D+40))^2 ≤
          1/(L^D) := by
      apply (div_le_div_iff₀ (pow_pos (pow_pos hLpos _) _)
        (pow_pos hLpos _)).mpr
      simpa only [one_mul] using hPowerLHS
    simpa [div_eq_mul_inv, inv_pow, mul_assoc,
      mul_comm, mul_left_comm] using hDiv
  have hInner :
      (130*U*W)*(B^2/U*W^16) =
        B^2*(130*W^17) := by
    field_simp
  have hCoeff : 0 ≤ B^2/U*W^16 := by
    positivity
  calc
    _ ≤ ((L^(E+D+40))⁻¹)^2 *
      ((130*U*W)*(B^2/U*W^16)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hPref hCoeff) (sq_nonneg _)
    _ = ((L^(E+D+40))⁻¹)^2 * (B^2*(130*W^17)) := by
      rw [hInner]
    _ ≤ ((L^(E+D+40))⁻¹)^2 * (B^2*L^39) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h39 (sq_nonneg B)) (sq_nonneg _)
    _ ≤ ((L^(E+D+40))⁻¹)^2 * ((L^E)^2 * L^39) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hB2 (pow_nonneg hLpos.le _))
        (sq_nonneg _)
    _ ≤ _ := hPower
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualMellinScaleBudget -/

section

namespace Green64Analytic.CorrelationMellin

/-! Direct source scale inequalities. The first converts the bound on
the threefactor product into a numerical log budget; the second
derives the Mellin time dominance T≤U from original H≫L*P. -/

theorem source_actual_dyadic_log_budget
    (L : ℝ) (N : ℕ)
    (hL : 3 ≤ L) (hN : 1 ≤ N)
    (hNexp : (N:ℝ) ≤ Real.exp (2*L)) :
    1+Real.log (N:ℝ) ≤ L^2 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hlog := Real.log_le_log hNpos hNexp
  rw [Real.log_exp] at hlog
  nlinarith [sq_nonneg (L-3)]

theorem source_actual_mellin_time_core_scale
    (L Y H P U T C : ℝ)
    (hL : 0 ≤ L) (hU : 0 ≤ U) (hH : 0 < H)
    (hY : Y ≤ C*P*U)
    (hHlarge : 2*L*C*P ≤ H)
    (hT : T = 2*L*Y/H) :
    T ≤ U := by
  rw [hT]
  apply (div_le_iff₀ hH).mpr
  have hFirst := mul_le_mul_of_nonneg_left hY
    (by positivity : 0 ≤ 2*L)
  have hSecond := mul_le_mul_of_nonneg_right hHlarge hU
  nlinarith
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualComparisonScaleSpecialization -/

section

namespace Green64Analytic.CorrelationMellin

/-! Explicit source-comparison normalization. H' is the product
of the two free comparison scales, H=H'/L^Carc and
U=M0*P0*R0 is the product of the three remaining dyadic scales.
The two required polynomial-budget inequalities are CONSEQUENCES
of the displayed comparison inequalities; they are not assumed. -/
theorem source_actual_comparison_scale_to_polynomial_budgets
    (L Y Hprime Psmall Ccomp Carc : ℝ) (M0 P0 R0 : ℕ)
    (hL : 3 ≤ L) (hY : 0 ≤ Y)
    (hPsmall : 1 ≤ Psmall)
    (hHprime : 0 < Hprime)
    (hYcompare :
      Y ≤ Ccomp*Psmall*((M0*P0*R0:ℕ):ℝ))
    (hUcompare :
      ((M0*P0*R0:ℕ):ℝ)*Psmall ≤ Ccomp*Y)
    (hFreeScale :
      2*L*Ccomp*Psmall*L^Carc ≤ Hprime)
    (hYscale : Y ≤ Real.exp (3*L/2))
    (hCmargin : 8*Ccomp ≤ Real.exp (L/2)) :
    2*L*Y/(Hprime/L^Carc) ≤ ((M0*P0*R0:ℕ):ℝ) ∧
    ((((2*M0)*(2*P0)*(2*R0):ℕ):ℝ) ≤ Real.exp (2*L)) := by
  let U : ℝ := ((M0*P0*R0:ℕ):ℝ)
  have hLpos : 0 < L := by linarith
  have hPpos : 0 < Psmall := by linarith
  have hU : 0 ≤ U := by dsimp [U]; exact Nat.cast_nonneg _
  have hArcPos : 0 < L^Carc := Real.rpow_pos_of_pos hLpos _
  have hH : 0 < Hprime/L^Carc := div_pos hHprime hArcPos
  have hHDom : 2*L*Ccomp*Psmall ≤ Hprime/L^Carc := by
    apply (le_div_iff₀ hArcPos).mpr
    nlinarith [hFreeScale]
  have hTime : 2*L*Y/(Hprime/L^Carc) ≤ U :=
    source_actual_mellin_time_core_scale
      L Y (Hprime/L^Carc) Psmall U
      (2*L*Y/(Hprime/L^Carc)) Ccomp
      (by linarith) hU hH hYcompare hHDom rfl
  have hExpPos : 0 ≤ Real.exp (L/2) := (Real.exp_pos _).le
  have hEight : 8*Ccomp ≤ Psmall*Real.exp (L/2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hPsmall) hExpPos]
  have hFirst : 8*U*Psmall ≤ 8*Ccomp*Y := by
    dsimp [U] at hUcompare ⊢
    nlinarith [hUcompare]
  have hSecond :
      8*Ccomp*Y ≤ Psmall*Real.exp (L/2)*Real.exp (3*L/2) := by
    calc
      _ ≤ (Psmall*Real.exp (L/2))*Y :=
        mul_le_mul_of_nonneg_right hEight hY
      _ ≤ (Psmall*Real.exp (L/2))*Real.exp (3*L/2) :=
        mul_le_mul_of_nonneg_left hYscale (by positivity)
  have hThird : 8*U*Psmall ≤ Psmall*Real.exp (2*L) := by
    calc
      _ ≤ 8*Ccomp*Y := hFirst
      _ ≤ Psmall*Real.exp (L/2)*Real.exp (3*L/2) := hSecond
      _ = Psmall*(Real.exp (L/2)*Real.exp (3*L/2)) := by ring
      _ = Psmall*Real.exp (2*L) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hExp : 8*U ≤ Real.exp (2*L) := by
    by_contra hn
    have hDiff : 0 < 8*U - Real.exp (2*L) := by linarith
    have hContra := mul_pos hDiff hPpos
    nlinarith [hThird]
  have hCast :
      (((2*M0)*(2*P0)*(2*R0):ℕ):ℝ) = 8*U := by
    dsimp [U]
    push_cast
    ring
  exact ⟨hTime, hCast.le.trans hExp⟩

/-- Intersecting the ORIGINAL alpha with a source dyad never
increases its coefficient budget, even if the interval is empty. -/
theorem source_actual_alpha_dyadic_cut_coeff_budget
    (alpha : ℕ → ℂ) (lo hi a b : ℕ) (A : ℝ)
    (hA : 0 ≤ A)
    (hAlpha : ∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ A) :
    ∀ m ∈ Finset.Icc a b,
      ‖sourceAlphaDyadicCut alpha lo hi m‖ ≤ A := by
  intro m hm
  by_cases h : m ∈ Finset.Icc lo hi
  · simpa [sourceAlphaDyadicCut, h] using hAlpha m h
  · simpa [sourceAlphaDyadicCut, h] using hA
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualComparisonScaleEventually -/

section

open Filter
namespace Green64Analytic.CorrelationMellin

/-! The fixed source comparison constant is absorbed by exp(L/2)
for all sufficiently large logarithmic scales L. -/
theorem eventually_source_comparison_exponential_margin
    (Ccomp : ℝ) :
    ∀ᶠ L : ℝ in atTop, 8*Ccomp ≤ Real.exp (L/2) := by
  have hDiv : Tendsto (fun L : ℝ => L/2) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (by norm_num : (0:ℝ)<2)).2 tendsto_id
  exact (Real.tendsto_exp_atTop.comp hDiv).eventually
    (eventually_ge_atTop (8*Ccomp))

/-- The two polynomial budgets follow EVENTUALLY from the original
comparison inequalities, without an extra fixed-size margin hypothesis. -/
theorem eventually_source_comparison_to_polynomial_budgets
    (Ccomp : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (Y Hprime Psmall Carc : ℝ) (M0 P0 R0 : ℕ),
      3 ≤ L → 0 ≤ Y → 1 ≤ Psmall → 0 < Hprime →
      Y ≤ Ccomp*Psmall*((M0*P0*R0:ℕ):ℝ) →
      ((M0*P0*R0:ℕ):ℝ)*Psmall ≤ Ccomp*Y →
      2*L*Ccomp*Psmall*L^Carc ≤ Hprime →
      Y ≤ Real.exp (3*L/2) →
      2*L*Y/(Hprime/L^Carc) ≤ ((M0*P0*R0:ℕ):ℝ) ∧
      ((((2*M0)*(2*P0)*(2*R0):ℕ):ℝ) ≤ Real.exp (2*L)) := by
  filter_upwards [eventually_source_comparison_exponential_margin Ccomp]
    with L hMargin
  intro Y Hprime Psmall Carc M0 P0 R0
    hL hY hPsmall hHprime hYcompare hUcompare hFreeScale hYscale
  exact source_actual_comparison_scale_to_polynomial_budgets
    L Y Hprime Psmall Ccomp Carc M0 P0 R0
    hL hY hPsmall hHprime hYcompare hUcompare hFreeScale
    hYscale hMargin
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualMellinWindowSource -/

section

namespace Green64Analytic.CorrelationMellin

/-! The actual source Mellin time T=2LY/H is shorter than
the coefficient support scale Y once H'=H*L^Carc dominates 4L.
This is the high-U1 hypothesis T+2<=Y, proved from the
original free comparison product scale rather than assumed. -/
theorem source_actual_mellin_time_plus_two_below_Y
    (L Y Hprime Carc : ℝ)
    (hL : 0 < L) (hY : 4 ≤ Y)
    (hHprime : 0 < Hprime)
    (hFree : 4*L*L^Carc ≤ Hprime) :
    (2*L*Y/(Hprime/L^Carc))+2 ≤ Y := by
  have hPowPos : 0 < L^Carc :=
    Real.rpow_pos_of_pos hL _
  have hH : 0 < Hprime/L^Carc := div_pos hHprime hPowPos
  have hHL : 4*L ≤ Hprime/L^Carc := by
    apply (le_div_iff₀ hPowPos).mpr
    nlinarith [hFree]
  have hYnonneg : 0 ≤ Y/2 := by linarith
  have hHalf : 2*L*Y/(Hprime/L^Carc) ≤ Y/2 := by
    apply (div_le_iff₀ hH).mpr
    have hh := mul_le_mul_of_nonneg_right hHL hYnonneg
    nlinarith [hh]
  linarith

/-- The same bound for the actual Nat.ceil Y support parameter of U1. -/
theorem source_actual_mellin_time_plus_two_below_nat_ceil_Y
    (L Y Hprime Carc : ℝ)
    (hL : 0 < L) (hY : 4 ≤ Y)
    (hHprime : 0 < Hprime)
    (hFree : 4*L*L^Carc ≤ Hprime) :
    (2*L*Y/(Hprime/L^Carc))+2 ≤ (⌈Y⌉₊:ℝ) := by
  exact (source_actual_mellin_time_plus_two_below_Y
    L Y Hprime Carc hL hY hHprime hFree).trans (Nat.le_ceil Y)
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualU1ProductScale -/

section

namespace Green64Analytic.CorrelationMellin

/-! The 3/5 lower product threshold used by physical high U1
is implied by the source four-factor box comparability once
the short and long prime scales occupy at most Y^(2/5).
This does NOT assume M0*R0 >= Y^(3/5) separately. -/
theorem source_actual_comparison_to_U1_residual_lower
    (Y C Psmall Pprime : ℝ) (M0 R0 : ℕ)
    (hY : 0 < Y)
    (hCompare :
      Y ≤ (C*Psmall*Pprime)*((M0*R0:ℕ):ℝ))
    (hPrimeScales : C*Psmall*Pprime ≤ Y^(2/5:ℝ)) :
    Y^(3/5:ℝ) ≤ ((M0*R0:ℕ):ℝ) := by
  let U : ℝ := ((M0*R0:ℕ):ℝ)
  have hU : 0 ≤ U := by dsimp [U]; exact Nat.cast_nonneg _
  have hShort :
      Y ≤ Y^(2/5:ℝ)*U :=
    hCompare.trans (mul_le_mul_of_nonneg_right hPrimeScales hU)
  have hDen : 0 < Y^(2/5:ℝ) := Real.rpow_pos_of_pos hY _
  have hDiv : Y / Y^(2/5:ℝ) ≤ U :=
    (div_le_iff₀ hDen).mpr (by simpa only [mul_comm] using hShort)
  have hPow :
      Y^(3/5:ℝ) = Y / Y^(2/5:ℝ) := by
    simpa [show (1:ℝ)-(2/5:ℝ)=(3/5:ℝ) by norm_num] using
      (Real.rpow_sub hY (1:ℝ) (2/5:ℝ))
  simpa only [U,hPow] using hDiv
end Green64Analytic.CorrelationMellin

end

/-! ## SourceOrderedAtomNormalization -/

section

namespace Green64Analytic.SourceAtomLabels
open scoped BigOperators

/-- Actual one-slot source prime label law μ(p)=1/(p V).
The underlying finite index consists of precisely the labels in S. -/
noncomputable def labelWeight
    (S : Finset ℕ) (V : ℝ) (p : {p : ℕ // p ∈ S}) : ℝ :=
  (1/(p.val:ℝ))/V

/-- A source ordered k-tuple has independent labels, repetitions
permitted exactly as in the ideal/source product sampling law. -/
noncomputable def orderedLabelMass
    (S : Finset ℕ) (V : ℝ) (k : ℕ)
    (f : Fin k → {p : ℕ // p ∈ S}) : ℝ :=
  ∏ i : Fin k, labelWeight S V (f i)

noncomputable def orderedLabelProduct
    (S : Finset ℕ) (k : ℕ)
    (f : Fin k → {p : ℕ // p ∈ S}) : ℕ :=
  ∏ i : Fin k, (f i).val

theorem single_label_law_normalized
    (S : Finset ℕ) (V : ℝ)
    (hV : V = ∑ p ∈ S, (1/(p:ℝ)))
    (hVp : V ≠ 0) :
    (∑ p : {p : ℕ // p ∈ S}, labelWeight S V p) = 1 := by
  classical
  letI : Fintype {p : ℕ // p ∈ S} := S.fintypeCoeSort
  have hsum :
      (∑ p : {p : ℕ // p ∈ S}, (1/(p.val:ℝ))) = V := by
    change (∑ p ∈ S.attach, (1/(p.val:ℝ))) = V
    exact (Finset.sum_attach S (fun q : ℕ => (1/(q:ℝ)))).trans hV.symm
  calc
    (∑ p : {p : ℕ // p ∈ S}, labelWeight S V p) =
      (∑ p : {p : ℕ // p ∈ S}, (1/(p.val:ℝ)))/V := by
        simp only [labelWeight, Finset.sum_div]
    _ = V/V := by rw [hsum]
    _ = 1 := by field_simp

theorem ordered_label_law_normalized
    (S : Finset ℕ) (V : ℝ) (k : ℕ)
    (hV : V = ∑ p ∈ S, (1/(p:ℝ)))
    (hVp : V ≠ 0) :
    (∑ f : Fin k → {p : ℕ // p ∈ S},
      orderedLabelMass S V k f) = 1 := by
  classical
  letI : Fintype {p : ℕ // p ∈ S} := S.fintypeCoeSort
  have hsingle := single_label_law_normalized S V hV hVp
  have hpi := Fintype.prod_sum (f := fun (_ : Fin k)
      (p : {p : ℕ // p ∈ S}) => labelWeight S V p)
  calc
    (∑ f : Fin k → {p : ℕ // p ∈ S},
      orderedLabelMass S V k f) =
        ∏ i : Fin k, ∑ p : {p : ℕ // p ∈ S}, labelWeight S V p := by
          simpa only [orderedLabelMass] using hpi.symm
    _ = ∏ _i : Fin k, (1:ℝ) := by simp only [hsingle]
    _ = 1 := by simp
/-- The map to the actual integer product loses tuple ordering, but
its fiber sums retain exact mass 1; no injectivity or squarefreeness
of the products is assumed. -/
theorem ordered_label_product_pushforward_normalized
    (S : Finset ℕ) (V : ℝ) (k : ℕ)
    (hV : V = ∑ p ∈ S, (1/(p:ℝ)))
    (hVp : V ≠ 0) :
    let D := {p : ℕ // p ∈ S}
    let T : Finset (Fin k → D) := Finset.univ
    let product : (Fin k → D) → ℕ :=
        orderedLabelProduct S k
    let atom : ℕ → ℝ := fun n =>
      ∑ f ∈ T.filter (fun f => product f = n),
        orderedLabelMass S V k f
    (∑ n ∈ T.image product, atom n) = 1 := by
  classical
  letI : Fintype {p : ℕ // p ∈ S} := S.fintypeCoeSort
  dsimp only
  let T : Finset (Fin k → {p : ℕ // p ∈ S}) := Finset.univ
  let product := orderedLabelProduct S k
  let atom : ℕ → ℝ := fun n =>
    ∑ f ∈ T.filter (fun f => product f = n),
      orderedLabelMass S V k f
  have hfiber (f : Fin k → {p : ℕ // p ∈ S}) (hf : f ∈ T) :
      atom (product f) =
        ∑ g ∈ T.filter (fun g => product g = product f),
          orderedLabelMass S V k g := rfl
  have h := Finset.sum_image'
    (s := T) (g := product)
    (f := atom) (fun f => orderedLabelMass S V k f) hfiber
  calc
    (∑ n ∈ T.image product, atom n) =
      ∑ f ∈ T, orderedLabelMass S V k f := h
    _ = (∑ f : Fin k → {p : ℕ // p ∈ S},
        orderedLabelMass S V k f) := by rfl
    _ = 1 := ordered_label_law_normalized S V k hV hVp
end Green64Analytic.SourceAtomLabels

end

/-! ## SourceLabeledMarginals -/

section

namespace Green64Analytic.SourceAtomLabels
open scoped BigOperators

/-- Every marginal of a normalized finite labeled law remains ≤1,
even when many different ordered histories collapse to the same
integer product. This is an exact combinatorial probability bridge. -/
theorem normalized_finite_pushforward_marginal
    {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (prod : ι → ℕ) (w : ι → ℝ)
    (F : Finset ℕ)
    (hw : ∀ i ∈ T, 0 ≤ w i)
    (hnorm : (∑ i ∈ T, w i) = 1) :
    (∑ n ∈ F, ∑ i ∈ T.filter (fun i => prod i = n), w i) ≤ 1 := by
  classical
  have hfilter : T.filter (fun i => prod i ∈ F) ⊆ T :=
    Finset.filter_subset _ _
  calc
    (∑ n ∈ F, ∑ i ∈ T.filter (fun i => prod i = n), w i) =
      ∑ i ∈ T.filter (fun i => prod i ∈ F), w i := by
        exact Finset.sum_fiberwise_eq_sum_filter T F prod w
    _ ≤ ∑ i ∈ T, w i :=
      Finset.sum_le_sum_of_subset_of_nonneg hfilter
        (fun i hiT hinot => hw i hiT)
    _ = 1 := hnorm

/-- Consequence for a genuine independent k-slot source group:
the distribution of the integer product is a normalized probability
and every arbitrary product-value window has mass at most one. -/
theorem source_ordered_product_marginal_le_one
    (S : Finset ℕ) (V : ℝ) (k : ℕ) (F : Finset ℕ)
    (hV : V = ∑ p ∈ S, (1/(p:ℝ)))
    (hVp : 0 < V) :
    let D := {p : ℕ // p ∈ S}
    let T : Finset (Fin k → D) := Finset.univ
    (∑ n ∈ F, ∑ f ∈ T.filter
      (fun f => orderedLabelProduct S k f = n),
        orderedLabelMass S V k f) ≤ 1 := by
  classical
  letI : Fintype {p : ℕ // p ∈ S} := S.fintypeCoeSort
  dsimp only
  let T : Finset (Fin k → {p : ℕ // p ∈ S}) := Finset.univ
  have hw (f : Fin k → {p : ℕ // p ∈ S}) (hf : f ∈ T) :
      0 ≤ orderedLabelMass S V k f := by
    unfold orderedLabelMass
    apply Finset.prod_nonneg
    intro i hi
    unfold labelWeight
    positivity
  have hn : (∑ f ∈ T, orderedLabelMass S V k f) = 1 := by
    simpa [T] using
      ordered_label_law_normalized S V k hV hVp.ne'
  exact normalized_finite_pushforward_marginal
    T (orderedLabelProduct S k)
    (orderedLabelMass S V k) F hw hn
end Green64Analytic.SourceAtomLabels

end

/-! ## SourceIndependentGroups -/

section

namespace Green64Analytic.SourceAtomLabels
open scoped BigOperators

/-- Independent source groups have exact total mass one for
arbitrary group-dependent finite tuple spaces and arbitrary slot
counts. No disjointness or injectivity of their integer product is
needed for normalization of the ordered configuration space. -/
theorem independent_group_tuple_law_normalized
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (D : γ → Type*) [∀ g, Fintype (D g)]
    (w : ∀ g, D g → ℝ)
    (h : ∀ g, (∑ x : D g, w g x) = 1) :
    (∑ f : (∀ g, D g), ∏ g, w g (f g)) = 1 := by
  classical
  calc
    (∑ f : (∀ g, D g), ∏ g, w g (f g)) =
       ∏ g, (∑ x : D g, w g x) := by
         exact (Fintype.prod_sum w).symm
    _ = ∏ _g : γ, (1:ℝ) := by simp only [h]
    _ = 1 := by simp

/-- The complete source big-group ordered-history law remains
normalized after mapping all group histories to a single integer
product, with any permitted collisions between histories. -/
theorem independent_group_product_pushforward_marginal
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (D : γ → Type*) [∀ g, Fintype (D g)]
    (w : ∀ g, D g → ℝ)
    (prod : (∀ g, D g) → ℕ) (F : Finset ℕ)
    (hn : ∀ g, (∑ x : D g, w g x) = 1)
    (hw : ∀ g, ∀ x : D g, 0 ≤ w g x) :
    (∑ n ∈ F, ∑ f ∈ (Finset.univ : Finset (∀ g, D g)).filter
      (fun f => prod f = n), ∏ g, w g (f g)) ≤ 1 := by
  classical
  let T : Finset (∀ g, D g) := Finset.univ
  have hnonneg (f : (∀ g, D g)) (hf : f ∈ T) :
      0 ≤ (∏ g, w g (f g)) := by
    apply Finset.prod_nonneg
    intro g hg
    exact hw g (f g)
  have hsum : (∑ f ∈ T, ∏ g, w g (f g)) = 1 := by
    simpa only [T] using independent_group_tuple_law_normalized D w hn
  exact normalized_finite_pushforward_marginal
    T prod (fun f => ∏ g, w g (f g)) F hnonneg hsum
end Green64Analytic.SourceAtomLabels

end

/-! ## SourceOriginalActualDyadicCount -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Explicit number of clipped dyadic boxes sufficient to cover
the actual source03 BIG prime group with p <= exp(L^d).
This is not an arbitrary n assumed to be small. -/
noncomputable def sourceOriginalSWDyadicCount434 (L d : ℝ) : ℕ :=
  ⌈L^d / Real.log 2⌉₊

/-- The actual exp(L^d) upper prime bound is covered by the
same dyadic decomposition used by the original Gram proof.
Only positivity of the genuine lower physical band endpoint is
needed. -/
theorem source_original_actual_SW_dyadic_count_cover434
    (L d : ℝ) (hL : 1 ≤ L) (u v : ℕ) (hu : 1 ≤ u)
    (hv : (v:ℝ) ≤ Real.exp (L^d)) :
    v ≤ u*2^(sourceOriginalSWDyadicCount434 L d) := by
  let n := sourceOriginalSWDyadicCount434 L d
  have hlog2 : 0 < Real.log (2:ℝ) :=
    Real.log_pos (by norm_num)
  have hceil : L^d / Real.log 2 ≤ (n:ℝ) := by
    exact Nat.le_ceil (L^d / Real.log 2)
  have hexp : L^d ≤ (n:ℝ)*Real.log 2 :=
    (div_le_iff₀ hlog2).mp hceil
  have hexpPow :
      Real.exp ((n:ℝ)*Real.log 2) = (2:ℝ)^n := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ) < 2)] using
      (Real.exp_nat_mul (Real.log 2) n)
  have hexpUpper : Real.exp (L^d) ≤ (2:ℝ)^n := by
    calc
      _ ≤ Real.exp ((n:ℝ)*Real.log 2) :=
        Real.exp_le_exp.mpr hexp
      _ = (2:ℝ)^n := hexpPow
  have hvPow : v ≤ 2^n := by
    exact_mod_cast hv.trans hexpUpper
  calc
    v ≤ 2^n := hvPow
    _ = 1*2^n := by simp
    _ ≤ u*2^n := Nat.mul_le_mul_right _ hu

/-- The TRUE dyadic-box count grows only as L^d, not exp(L^d).
The harmless constant 1+(log 2)^{-1} is independent of any
character or moving product-log cell. -/
theorem source_original_actual_SW_dyadic_count_power434
    (L d : ℝ) (hL : 1 ≤ L) (hd : 0 ≤ d) :
    ((sourceOriginalSWDyadicCount434 L d:ℕ):ℝ) ≤
      ((Real.log 2)⁻¹+1)*L^d := by
  let n := sourceOriginalSWDyadicCount434 L d
  have hlog2 : 0 < Real.log (2:ℝ) :=
    Real.log_pos (by norm_num)
  have hLpos : 0 ≤ L := by linarith
  have harg : 0 ≤ L^d / Real.log 2 :=
    div_nonneg (Real.rpow_nonneg hLpos _) hlog2.le
  have hceil : (n:ℝ) < L^d / Real.log 2 + 1 := by
    exact Nat.ceil_lt_add_one harg
  have hLpow : (1:ℝ) ≤ L^d := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hL hd
    simpa using hpow
  calc
    (n:ℝ) ≤ L^d / Real.log 2+1 := hceil.le
    _ = L^d*(Real.log 2)⁻¹+1 := by ring
    _ ≤ L^d*(Real.log 2)⁻¹ + L^d := by linarith
    _ = ((Real.log 2)⁻¹+1)*L^d := by ring
end Green64Analytic.CorrelationSquare

end

